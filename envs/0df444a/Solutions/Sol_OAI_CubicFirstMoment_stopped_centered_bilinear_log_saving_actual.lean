-- Prove2me | solution 1 for OAI.CubicFirstMoment.stopped_centered_bilinear_log_saving_actual
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:46:22.670339+00:00
-- url     : https://prove2.me/submissions/598859b4-5018-4e1c-a571-e30dd286508b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A013
import Definitions.Def_OAIQ096A015
import Definitions.Def_OAIQ096A016
import Theorems.Thm_OAI_CubicFirstMoment_stopped_sieved_model_log_saving
import Theorems.Thm_OAI_CubicFirstMoment_stopped_typeI_mixed_actual

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_GramPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment
end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Mobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_FullCubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_SieveMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergent norm series on the Eisenstein lattice

These elementary lattice bounds provide a quantitative tail for the
Möbius residue sum after square-divisor truncation.
-/

noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment

lemma norm_rpow_tail_pointwise {D s t : ℝ} (hD : 0 < D) (hst : s < t)
    {a : Eisenstein} (ha : D < norm a) :
    norm a^(-t) ≤ D^(s-t)*norm a^(-s) := by
  have hn : 0 < norm a := hD.trans ha
  calc
    _ = norm a^(s-t)*norm a^(-s) := by
      rw [← Real.rpow_add hn]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hD ha.le (by linarith))
      (Real.rpow_nonneg hn.le _)

/-- A stronger convergent exponent gives a power tail without losing a
factor to the norm fibers. -/
theorem eisenstein_norm_rpow_tail {D s t : ℝ} (hD : 0 < D)
    (hs : 1 < s) (hst : s < t) :
    (∑' a : Eisenstein, if D < norm a then norm a^(-t) else 0) ≤
      D^(s-t)*(∑' a : Eisenstein, norm a^(-s)) := by
  have ht := summable_eisenstein_norm_rpow (hs.trans hst)
  have htail := ht.indicator (fun a => D < norm a)
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ htail ((summable_eisenstein_norm_rpow hs).mul_left _)
  intro a
  change (if D < norm a then norm a^(-t) else 0) ≤ D^(s-t)*norm a^(-s)
  by_cases ha : D < norm a
  · simpa only [ha,ite_true, if_true] using norm_rpow_tail_pointwise hD hst ha
  · simp only [ha,ite_false, if_false]
    exact mul_nonneg (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg (norm_nonneg a) _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SchwartzLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
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

lemma traceFourier_zero (F : ℂ → ℂ) : traceFourier F 0 = ∫ z : ℂ, F z := by
  simp [traceFourier,tracePair]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLatticeProfile
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual angular annulus is a smooth compactly supported plane
function. Its area integral is zero in every nonzero integral mode. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff SchwartzMap Topology
namespace CubicFirstMoment

lemma angularPlanePhase_mul (ℓ : ℤ) (z w : ℂ) :
    angularPlanePhase ℓ (z*w) = angularPlanePhase ℓ z*angularPlanePhase ℓ w := by
  simp only [angularPlanePhase,norm_mul,Complex.ofReal_mul]
  rw [mul_div_mul_comm,mul_zpow]

lemma angularPlanePhase_coe (ℓ : ℤ) (a : Eisenstein) :
    angularPlanePhase ℓ (a:ℂ) = theta ℓ a := rfl

end CubicFirstMoment

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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimaryLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cancellation on the actual primary congruence class. The annulus
has zero area, and scaled coset Poisson summation controls every length. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

lemma angularPlanePhase_pos_mul (ℓ : ℤ) {s : ℝ} (hs : 0 < s) (z : ℂ) :
    angularPlanePhase ℓ ((s:ℂ)*z) = angularPlanePhase ℓ z := by
  rw [angularPlanePhase_mul]
  have he : angularPlanePhase ℓ (s:ℂ) = 1 := by
    simp [angularPlanePhase,Complex.norm_real,abs_of_pos hs,hs.ne']
  rw [he,one_mul]

lemma angularAnnulus_scaled (ℓ : ℤ) (W : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (a : Eisenstein) :
    angularAnnulus ℓ W (((1/Real.sqrt Y:ℝ):ℂ)*(a:ℂ)) =
      theta ℓ a*W (norm a/Y) := by
  have hs : 0 < 1/Real.sqrt Y := by positivity
  have hn : Complex.normSq (((1/Real.sqrt Y:ℝ):ℂ)*(a:ℂ)) = norm a/Y := by
    rw [Complex.normSq_mul,Complex.normSq_ofReal]
    change (1/Real.sqrt Y)*(1/Real.sqrt Y)*norm a = norm a/Y
    rw [one_div,←mul_inv,←pow_two,Real.sq_sqrt hY.le]
    ring
  rw [angularAnnulus,angularPlanePhase_pos_mul ℓ hs,angularPlanePhase_coe,hn]

lemma primary_scaled_coset (F : ℂ → ℂ) (s : ℂ) :
    (∑' u : PrimaryArgument, F (s*(u:ℂ))) =
      ∑' a : Eisenstein, F (s+(s*3)*(a:ℂ)) := by
  let e := Equiv.ofBijective (primaryCosetMap 1 primary_one)
    (primaryCosetMap_bijective 1 primary_one)
  have he := e.tsum_eq (fun u : PrimaryArgument => F (s*(u:ℂ)))
  change (∑' a : Eisenstein, F (s*((primaryCosetMap 1 primary_one a:PrimaryArgument):ℂ))) = _ at he
  have h3 : ((3:Eisenstein):ℂ) = 3 := map_ofNat eisensteinRing.val 3
  simpa [primaryCosetMap,mul_add,mul_assoc,h3] using he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularCoprimeLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coprimality removal for the angular lattice model. The
primary congruence class and all divisor phases remain literal. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryAngularLattice_eq_indicator (ℓ : ℤ) (W : ℝ → ℂ) (Y : ℝ) :
    primaryAngularLattice ℓ W Y =
      ∑' u : Eisenstein, if primary u then theta ℓ u*W (norm u/Y) else 0 := by
  symm
  change (∑' u : Eisenstein, Set.indicator {u | primary u}
    (fun u => theta ℓ u*W (norm u/Y)) u) = _
  rw [←tsum_subtype]
  rfl

lemma summable_primary_angular_restricted (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hsm : ContDiff ℝ ∞ W) {Y : ℝ} (hY : 0 < Y)
    (P : Eisenstein → Prop) :
    Summable (fun u : Eisenstein => if primary u ∧ P u then theta ℓ u*W (norm u/Y) else 0) := by
  apply (schwartz_summable_eisenstein (normProfileSchwartz W hW hsm Y hY)).norm.of_norm_bounded
  intro u
  change ‖ite _ _ _‖ ≤ ‖W (norm u/Y)‖
  split_ifs with hu
  · rw [norm_mul,norm_theta (primary_ne_zero hu.1),one_mul]
  · simp

lemma primaryAngularLattice_divisor (ℓ : ℤ) (W : ℝ → ℂ) (Y : ℝ)
    {d : Eisenstein} (hd : primary d) :
    (∑' u : Eisenstein, if primary u ∧ d ∣ u then theta ℓ u*W (norm u/Y) else 0) =
      theta ℓ d*primaryAngularLattice ℓ W (Y/norm d) := by
  rw [tsum_primary_dvd_eq_multiples hd,primaryAngularLattice_eq_indicator,←tsum_mul_left]
  apply tsum_congr
  intro u
  by_cases hu : primary u
  · simp only [hu,ite_true, if_true,theta_mul,norm_mul_eq]
    have hn : norm d ≠ 0 := ne_of_gt (norm_pos_of_ne_zero (primary_ne_zero hd))
    have he : norm d*norm u/Y = norm u/(Y/norm d) := by field_simp
    rw [he]
    ring
  · simp only [hu,ite_false, if_false,mul_zero]

lemma primaryCoprimeAngularLattice_expansion {r : Eisenstein}
    (hr : primary r) (hsr : Squarefree r) (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hsm : ContDiff ℝ ∞ W) {Y : ℝ} (hY : 0 < Y) :
    primaryCoprimeAngularLattice r ℓ W Y =
      ∑ s ∈ (primaryPrimeFactors r).powerset,
        (idealMoebius (∏ p ∈ s, p):ℂ)*theta ℓ (∏ p ∈ s, p)*
          primaryAngularLattice ℓ W (Y/norm (∏ p ∈ s, p)) := by
  let P := (primaryPrimeFactors r).powerset
  let f : Finset Eisenstein → Eisenstein → ℂ := fun s u =>
    (idealMoebius (∏ p ∈ s, p):ℂ)*
      (if primary u ∧ (∏ p ∈ s, p) ∣ u then theta ℓ u*W (norm u/Y) else 0)
  have hf (s : Finset Eisenstein) (_hs : s ∈ P) : Summable (f s) :=
    (summable_primary_angular_restricted ℓ W hW hsm hY _).mul_left _
  have he (u : Eisenstein) :
      (if primary u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0) =
        ∑ s ∈ P, f s u := by
    by_cases hu : primary u
    · have hi := congrArg (fun z : ℂ => z*(theta ℓ u*W (norm u/Y)))
        (primary_moebius_coprimality hr hsr u)
      rw [Finset.sum_mul] at hi
      calc
        _ = (if IsCoprime r u then (1:ℂ) else 0)*(theta ℓ u*W (norm u/Y)) := by
          by_cases hc : IsCoprime r u <;> simp [hu,hc]
        _ = _ := hi
        _ = _ := by
          apply Finset.sum_congr rfl
          intro s hs
          by_cases hd : (∏ p ∈ s, p) ∣ u <;> simp [f,hu,hd]
    · simp [f,hu]
  unfold primaryCoprimeAngularLattice
  simp_rw [he]
  rw [Summable.tsum_finsetSum hf]
  apply Finset.sum_congr rfl
  intro s hs
  have hd : primary (∏ p ∈ s, p) := primary_finset_prod _ _
    (fun p hp => (primaryPrimeFactor_spec hr (Finset.mem_powerset.mp hs hp)).1.1)
  change (∑' u : Eisenstein, (idealMoebius (∏ p ∈ s, p):ℂ)*_) = _
  rw [tsum_mul_left,primaryAngularLattice_divisor ℓ W Y hd]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

/-- The correction subtracts the factored model exactly, with the true
squarefree weight on the outer variable. Removing common prime factors
from the model is a separate arithmetic step. -/
theorem corrected_bilinear_identity (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ)
    (hA : ∀ a ∈ A, primary a) (hB : ∀ b ∈ B, primary b) :
    (∑ a ∈ A, ∑ b ∈ B, α a * β b * gauss (a * b) * normTwist u (a * b)) -
      (cStar : ℂ) * dispersionModel B β u *
        (∑ a ∈ A, α a * normTwist u a *
          (if Squarefree a then (1 : ℂ) else 0) * ((norm a ^ (-1 / 6 : ℝ) : ℝ) : ℂ)) =
      ∑ a ∈ A, α a * normTwist u a * gauss a *
        correctedDispersionPolynomial B β u a := by
  rw [bilinear_gauss_eq_rows A B α β u hA hB, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  dsimp [correctedDispersionPolynomial]
  rw [← gauss_mul_star_squarefree (hA a ha)]
  simp only [starRingEnd_apply]
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The squarefree majorant in corrected dispersion

Only the positive variance term is majorized. The mixed and model terms
retain their actual Möbius-square weights.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma truncatedSquareDivisorSum_eq_one (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c) (h1 : 1 ∈ C) {a : Eisenstein} (ha : Squarefree a) :
    truncatedSquareDivisorSum C a = 1 := by
  unfold truncatedSquareDivisorSum
  calc
    _ = if (1 : Eisenstein)^2 ∣ a then (idealMoebius 1 : ℝ) else 0 := by
      apply Finset.sum_eq_single 1
      · intro c hc hc1
        have hd : ¬c^2 ∣ a := by
          intro hd
          exact hc1 (primary_unit_eq_one (ha c (by simpa only [pow_two] using hd)) (hC c hc))
        simp [hd]
      · exact fun hn => (hn h1).elim
    _ = 1 := by simp [idealMoebius]

/-- This majorizes the true squarefree indicator and is exactly one on
squarefree elements. It applies to every truncation containing one. -/
theorem squarefree_le_truncated_majorant (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c) (h1 : 1 ∈ C) (a : Eisenstein) :
    (idealMoebius a : ℝ)^2 ≤ (truncatedSquareDivisorSum C a)^2 := by
  rw [idealMoebius_sq]
  by_cases ha : Squarefree a
  · rw [ite_eq_left ha,truncatedSquareDivisorSum_eq_one C hC h1 ha]
    norm_num
  · rw [ite_eq_right ha]
    exact sq_nonneg _

/-- The positive term alone is enlarged in the corrected square. The two
remaining terms keep their original squarefree weights. -/
theorem corrected_squarefree_majorant (A C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c) (h1 : 1 ∈ C)
    (W : Eisenstein → ℝ) (hW : ∀ a ∈ A, 0 ≤ W a)
    (F M : Eisenstein → ℂ) :
    (∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*‖F a-M a‖^2) ≤
      (∑ a ∈ A, (truncatedSquareDivisorSum C a)^2*W a*‖F a‖^2) -
        2*(∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*(star (F a)*M a).re) +
        ∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*‖M a‖^2 := by
  have he (x y : ℂ) : ‖x-y‖^2 = ‖x‖^2-2*(star x*y).re+‖y‖^2 := by
    simpa only [RCLike.inner_apply,starRingEnd_apply,mul_comm,RCLike.re_eq_complex_re,RCLike.re_eq_complex_re] using
      norm_sub_sq (𝕜 := ℂ) x y
  have hp : (∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*‖F a‖^2) ≤
      ∑ a ∈ A, (truncatedSquareDivisorSum C a)^2*W a*‖F a‖^2 := by
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (squarefree_le_truncated_majorant C hC h1 a) (hW a ha))
      (sq_nonneg _)
  have hx : (∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*‖F a-M a‖^2) =
      (∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*‖F a‖^2) -
        2*(∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*(star (F a)*M a).re) +
        ∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*‖M a‖^2 := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [he]
    ring
  rw [hx]
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeJoin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma join_factor_primaryPrime {a b p : Eisenstein} (ha : primary a) (hb : primary b)
    (hp : p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b) : primaryPrime p := by
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (primaryPrimeFactor_spec ha hp).1
  · exact (primaryPrimeFactor_spec hb hp).1

lemma primarySquarefreeJoin_primary {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    primary (primarySquarefreeJoin a b) :=
  primary_finset_prod _ _ (fun _p hp => (join_factor_primaryPrime ha hb hp).1)

lemma primarySquarefreeJoin_squarefree {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    Squarefree (primarySquarefreeJoin a b) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact isRelPrime_iff_isCoprime.mpr
      (primaryPrimes_isCoprime (join_factor_primaryPrime ha hb hp)
        (join_factor_primaryPrime ha hb hq) hpq)
  · intro p hp
    exact (join_factor_primaryPrime ha hb hp).2.squarefree

lemma dvd_primarySquarefreeJoin_left {a b : Eisenstein} (ha : primary a) (hsa : Squarefree a) :
    a ∣ primarySquarefreeJoin a b := by
  nth_rw 1 [← primaryPrimeFactors_prod ha hsa]
  exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left

lemma dvd_primarySquarefreeJoin_right {a b : Eisenstein} (hb : primary b) (hsb : Squarefree b) :
    b ∣ primarySquarefreeJoin a b := by
  nth_rw 1 [← primaryPrimeFactors_prod hb hsb]
  exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_right

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SieveCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Support and divisor bounds for the dispersion sieve coefficients

The coefficients are the actual finite least-common-multiple collection
of the truncated Möbius square, not an abstract majorant hypothesis.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma collectedSieveCoefficient_nonzero (C : Finset Eisenstein) (e : Eisenstein)
    (he : collectedSquarefreeSieveCoefficient C e ≠ 0) :
    ∃ a ∈ C, ∃ b ∈ C, primarySquarefreeJoin a b = e := by
  have hne : ((C.product C).filter (fun t => primarySquarefreeJoin t.1 t.2 = e)).Nonempty := by
    by_contra h
    apply he
    unfold collectedSquarefreeSieveCoefficient
    apply Finset.sum_eq_zero
    intro t ht
    exact (h ⟨t,ht⟩).elim
  obtain ⟨⟨a,b⟩,hab⟩ := hne
  have h := Finset.mem_filter.mp hab
  exact ⟨a,(Finset.mem_product.mp h.1).1,b,(Finset.mem_product.mp h.1).2,h.2⟩

lemma abs_idealMoebius_real_le_one (a : Eisenstein) : |(idealMoebius a : ℝ)| ≤ 1 := by
  simpa only [Complex.norm_intCast] using norm_idealMoebius_le_one a

/-- The number of possible ordered divisor pairs controls the collected
coefficient. This is the square-divisor bound required for the sieve. -/
theorem collectedSieveCoefficient_abs_le (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) (e : Eisenstein) :
    |collectedSquarefreeSieveCoefficient C e| ≤
      ((2 : ℝ)^(primaryPrimeFactors e).card)^2 := by
  by_cases he : collectedSquarefreeSieveCoefficient C e = 0
  · rw [he,abs_zero]
    exact sq_nonneg _
  have hprimary : primary e := by
    obtain ⟨a,ha,b,hb,hab⟩ := collectedSieveCoefficient_nonzero C e he
    rw [← hab]
    exact primarySquarefreeJoin_primary (hC a ha).1 (hC b hb).1
  let T := C.filter (· ∣ e)
  let F := (C.product C).filter (fun t => primarySquarefreeJoin t.1 t.2 = e)
  have hsub : F ⊆ T.product T := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    have ha := (Finset.mem_product.mp ht'.1).1
    have hb := (Finset.mem_product.mp ht'.1).2
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨ha,ht'.2 ▸ dvd_primarySquarefreeJoin_left (hC t.1 ha).1 (hC t.1 ha).2⟩
    · exact Finset.mem_filter.mpr ⟨hb,ht'.2 ▸ dvd_primarySquarefreeJoin_right (hC t.2 hb).1 (hC t.2 hb).2⟩
  have hT : (T.card : ℝ) ≤ (2 : ℝ)^(primaryPrimeFactors e).card :=
    primary_divisors_card_le C hC hprimary
  calc
    _ ≤ ∑ t ∈ F, |(idealMoebius t.1 : ℝ)*(idealMoebius t.2 : ℝ)| :=
      by simpa only [Real.norm_eq_abs,collectedSquarefreeSieveCoefficient,F,
          Finset.product_eq_sprod] using
        (norm_sum_le (s := F) (f := fun t => (idealMoebius t.1 : ℝ)*(idealMoebius t.2 : ℝ)))
    _ ≤ ∑ _t ∈ F, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul]
      have h := mul_le_mul (abs_idealMoebius_real_le_one t.1)
        (abs_idealMoebius_real_le_one t.2) (abs_nonneg _) (show (0:ℝ) ≤ 1 by norm_num)
      simpa only [mul_one] using h
    _ = (F.card : ℝ) := by simp
    _ ≤ ((T.product T).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = (T.card : ℝ)^2 := by
      have hh := congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_product T T)
      simpa only [Nat.cast_mul,pow_two,Finset.product_eq_sprod] using hh
    _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) hT 2

/-- The divisor loss is an arbitrarily small fixed power, uniformly in
all choices of the truncation set. -/
theorem collectedSieveCoefficient_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (C : Finset Eisenstein),
      (∀ c ∈ C, primary c ∧ Squarefree c) → ∀ e : Eisenstein,
      |collectedSquarefreeSieveCoefficient C e| ≤ K*norm e^ε := by
  obtain ⟨K,hK,hbound⟩ := primeDivisorWeight_small_power (ε/2) (by linarith)
  refine ⟨K^2,pow_pos hK _,?_⟩
  intro C hC e
  by_cases he : collectedSquarefreeSieveCoefficient C e = 0
  · rw [he,abs_zero]
    exact mul_nonneg (sq_nonneg K) (Real.rpow_nonneg (norm_nonneg e) ε)
  obtain ⟨a,ha,b,hb,hab⟩ := collectedSieveCoefficient_nonzero C e he
  have hep : primary e := hab ▸ primarySquarefreeJoin_primary (hC a ha).1 (hC b hb).1
  have hes : Squarefree e := hab ▸ primarySquarefreeJoin_squarefree (hC a ha).1 (hC b hb).1
  have hh := hbound e hep hes
  apply (collectedSieveCoefficient_abs_le C hC e).trans
  calc
    _ ≤ (K*norm e^(ε/2))^2 := pow_le_pow_left₀ (by positivity) hh 2
    _ = K^2*norm e^ε := by
      rw [mul_pow,← Real.rpow_natCast (norm e^(ε/2)) 2,← Real.rpow_mul (norm_nonneg e)]
      congr 2
      norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SieveMobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

private lemma insert_union_eq_iff {ι : Type*} [DecidableEq ι]
    {p : ι} {s t U : Finset ι} (hp : p ∉ U) (hs : s ⊆ U) (ht : t ⊆ U) :
    insert p (s ∪ t) = insert p U ↔ s ∪ t = U := by
  constructor
  · intro h
    have h' := congrArg (fun v : Finset ι => v.erase p) h
    have hpst : p ∉ s ∪ t := by simp only [Finset.mem_union,not_or]; exact ⟨fun h => hp (hs h),fun h => hp (ht h)⟩
    simpa [hpst,hp] using h'
  · exact congrArg (insert p)

private lemma union_step {ι : Type*} [DecidableEq ι]
    {p : ι} {s t U : Finset ι} (hp : p ∉ U) (hs : s ⊆ U) (ht : t ⊆ U) :
    (if s ∪ t = insert p U then (-1:ℝ)^s.card*(-1)^t.card else 0) +
    (if s ∪ insert p t = insert p U then (-1:ℝ)^s.card*(-1)^(insert p t).card else 0) +
    (if insert p s ∪ t = insert p U then (-1:ℝ)^(insert p s).card*(-1)^t.card else 0) +
    (if insert p s ∪ insert p t = insert p U then
      (-1:ℝ)^(insert p s).card*(-1)^(insert p t).card else 0) =
    -(if s ∪ t = U then (-1:ℝ)^s.card*(-1)^t.card else 0) := by
  have hps : p ∉ s := fun h => hp (hs h)
  have hpt : p ∉ t := fun h => hp (ht h)
  have hne : s ∪ t ≠ insert p U := by
    intro h
    have hm : p ∈ s ∪ t := h ▸ Finset.mem_insert_self p U
    rcases Finset.mem_union.mp hm with hm | hm
    · exact hps hm
    · exact hpt hm
  have hi := insert_union_eq_iff hp hs ht
  simp only [hne,ite_false, if_false,Finset.union_insert,Finset.insert_union,Finset.insert_idem,
    hi,Finset.card_insert_of_notMem hps,Finset.card_insert_of_notMem hpt,pow_succ]
  split_ifs <;> ring

/-- The exact union convolution of the signed subset weights. -/
theorem squarefree_mobius_union {ι : Type*} [DecidableEq ι] (U : Finset ι) :
    (∑ s ∈ U.powerset, ∑ t ∈ U.powerset,
      if s ∪ t = U then (-1:ℝ)^s.card*(-1)^t.card else 0) = (-1)^U.card := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert p U hp ih =>
    rw [Finset.sum_powerset_insert hp]
    simp_rw [Finset.sum_powerset_insert hp]
    calc
      _ = ∑ s ∈ U.powerset, ∑ t ∈ U.powerset,
          ((if s ∪ t = insert p U then (-1:ℝ)^s.card*(-1)^t.card else 0) +
          (if s ∪ insert p t = insert p U then (-1:ℝ)^s.card*(-1)^(insert p t).card else 0) +
          (if insert p s ∪ t = insert p U then (-1:ℝ)^(insert p s).card*(-1)^t.card else 0) +
          (if insert p s ∪ insert p t = insert p U then
            (-1:ℝ)^(insert p s).card*(-1)^(insert p t).card else 0)) := by
        simp only [Finset.sum_add_distrib]
        ring
      _ = ∑ s ∈ U.powerset, ∑ t ∈ U.powerset,
          -(if s ∪ t = U then (-1:ℝ)^s.card*(-1)^t.card else 0) := by
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro t ht
        exact union_step hp (Finset.mem_powerset.mp hs) (Finset.mem_powerset.mp ht)
      _ = -((-1:ℝ)^U.card) := by simp only [Finset.sum_neg_distrib,ih]
      _ = _ := by rw [Finset.card_insert_of_notMem hp,pow_succ]; ring

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

lemma primaryPrimeFactors_prod_injective {U : Finset Eisenstein}
    (hU : ∀ p ∈ U, primaryPrime p) :
    Set.InjOn (fun s : Finset Eisenstein => ∏ p ∈ s, p) (↑U.powerset : Set (Finset Eisenstein)) := by
  intro s hs t ht he
  have hs' := Finset.mem_powerset.mp hs
  have ht' := Finset.mem_powerset.mp ht
  have hh := congrArg primaryPrimeFactors he
  simpa only [primaryPrimeFactors_finset_prod s (fun p hp => hU p (hs' hp)),
    primaryPrimeFactors_finset_prod t (fun p hp => hU p (ht' hp))] using hh

lemma primaryPrime_product_squarefree (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) : Squarefree (∏ p ∈ U, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact isRelPrime_iff_isCoprime.mpr (primaryPrimes_isCoprime (hU p hp) (hU q hq) hpq)
  · intro p hp
    exact (hU p hp).2.squarefree

lemma collectedSieveCoefficient_restrict_divisors (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) (e : Eisenstein) :
    collectedSquarefreeSieveCoefficient C e =
      collectedSquarefreeSieveCoefficient (C.filter (· ∣ e)) e := by
  have hset : (C.product C).filter (fun t => primarySquarefreeJoin t.1 t.2 = e) =
      ((C.filter (· ∣ e)).product (C.filter (· ∣ e))).filter
        (fun t => primarySquarefreeJoin t.1 t.2 = e) := by
    ext t
    simp only [Finset.product_eq_sprod,Finset.mem_filter,Finset.mem_product]
    constructor
    · rintro ⟨⟨ha,hb⟩,he⟩
      refine ⟨⟨⟨ha,?_⟩,⟨hb,?_⟩⟩,he⟩
      · exact he ▸ dvd_primarySquarefreeJoin_left (hC t.1 ha).1 (hC t.1 ha).2
      · exact he ▸ dvd_primarySquarefreeJoin_right (hC t.2 hb).1 (hC t.2 hb).2
    · rintro ⟨⟨⟨ha,_⟩,⟨hb,_⟩⟩,he⟩
      exact ⟨⟨ha,hb⟩,he⟩
  unfold collectedSquarefreeSieveCoefficient
  rw [hset]

lemma primary_divisors_eq_subset_products (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) {e : Eisenstein}
    (he : primary e) (hcomplete : ∀ c, primary c → Squarefree c → c ∣ e → c ∈ C) :
    C.filter (· ∣ e) = (primaryPrimeFactors e).powerset.image (fun s => ∏ p ∈ s, p) := by
  ext c
  constructor
  · intro hc
    obtain ⟨hc,hce⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_image.mpr ⟨primaryPrimeFactors c,
      Finset.mem_powerset.mpr (primaryPrimeFactors_subset_of_dvd (hC c hc).1 he hce),
      primaryPrimeFactors_prod (hC c hc).1 (hC c hc).2⟩
  · intro hc
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hc
    have hsub := Finset.mem_powerset.mp hs
    have hsp : ∀ p ∈ s, primaryPrime p := fun p hp => (primaryPrimeFactor_spec he (hsub hp)).1
    have hp := primary_finset_prod s (fun p : Eisenstein => p) (fun p hp => (hsp p hp).1)
    have hd : (∏ p ∈ s, p) ∣ e :=
      (primary_subsets_prod_dvd he hsub e).mpr (fun p hp => (primaryPrimeFactor_spec he (hsub hp)).2)
    exact Finset.mem_filter.mpr ⟨hcomplete _ hp (primaryPrime_product_squarefree s hsp) hd,hd⟩

/-- If the truncation contains every divisor of `e`, the collected
coefficient is exactly the ideal Möbius function. -/
theorem collectedSieveCoefficient_eq_moebius (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) {e : Eisenstein}
    (he : primary e) (hse : Squarefree e)
    (hcomplete : ∀ c, primary c → Squarefree c → c ∣ e → c ∈ C) :
    collectedSquarefreeSieveCoefficient C e = (idealMoebius e : ℝ) := by
  let U := primaryPrimeFactors e
  have hU : ∀ p ∈ U, primaryPrime p := fun p hp => (primaryPrimeFactor_spec he hp).1
  have hinj := primaryPrimeFactors_prod_injective hU
  have hprod : (∏ p ∈ U, p) = e := primaryPrimeFactors_prod he hse
  rw [collectedSieveCoefficient_restrict_divisors C hC e,
    primary_divisors_eq_subset_products C hC he hcomplete]
  unfold collectedSquarefreeSieveCoefficient
  rw [Finset.sum_filter]
  simp only [Finset.product_eq_sprod,Finset.sum_product]
  change (∑ a ∈ U.powerset.image (fun s => ∏ p ∈ s, p),
    ∑ b ∈ U.powerset.image (fun s => ∏ p ∈ s, p),
      if primarySquarefreeJoin a b = e then (idealMoebius a : ℝ)*(idealMoebius b : ℝ) else 0) = _
  rw [Finset.sum_image hinj]
  have hex : (∑ s ∈ U.powerset, ∑ t ∈ U.powerset.image (fun v => ∏ p ∈ v, p),
      if primarySquarefreeJoin (∏ p ∈ s, p) t = e then
        (idealMoebius (∏ p ∈ s, p) : ℝ)*(idealMoebius t : ℝ) else 0) =
      ∑ s ∈ U.powerset, ∑ t ∈ U.powerset,
        if s ∪ t = U then (-1:ℝ)^s.card*(-1)^t.card else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro t ht
    have hsU := Finset.mem_powerset.mp hs
    have htU := Finset.mem_powerset.mp ht
    have hsP : ∀ p ∈ s, primaryPrime p := fun p hp => hU p (hsU hp)
    have htP : ∀ p ∈ t, primaryPrime p := fun p hp => hU p (htU hp)
    have hstP : ∀ p ∈ s ∪ t, primaryPrime p := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hsP p hp
      · exact htP p hp
    have hj : primarySquarefreeJoin (∏ p ∈ s, p) (∏ p ∈ t, p) = e ↔ s ∪ t = U := by
      unfold primarySquarefreeJoin
      rw [primaryPrimeFactors_finset_prod s hsP,primaryPrimeFactors_finset_prod t htP]
      constructor
      · intro h
        have hh := congrArg primaryPrimeFactors h
        simpa only [primaryPrimeFactors_finset_prod (s ∪ t) hstP] using hh
      · intro h
        rw [h,hprod]
    simp only [hj,idealMoebius_prod_primaryPrimes s hsP,idealMoebius_prod_primaryPrimes t htP,
      Int.cast_pow,Int.cast_neg,Int.cast_one]
  rw [hex,squarefree_mobius_union]
  rw [← hprod,idealMoebius_prod_primaryPrimes U hU]
  push_cast
  rfl

lemma mem_squarefreeDivisorTruncation {D : ℝ} {c : Eisenstein} :
    c ∈ squarefreeDivisorTruncation D ↔ primary c ∧ Squarefree c ∧ norm c ≤ D := by
  simp only [squarefreeDivisorTruncation,squareDivisorTruncation,Finset.mem_filter,
    mem_nonzeroNormBall]
  constructor
  · rintro ⟨⟨⟨hn,_⟩,hp⟩,hs⟩
    exact ⟨hp,hs,hn⟩
  · rintro ⟨hp,hs,hn⟩
    exact ⟨⟨⟨hn,primary_ne_zero hp⟩,hp⟩,hs⟩

/-- The exact low-divisor identity for the concrete norm truncation. -/
theorem squarefreeSieveCoefficient_small {D : ℝ} {e : Eisenstein}
    (he : primary e) (hse : Squarefree e) (hD : norm e ≤ D) :
    collectedSquarefreeSieveCoefficient (squarefreeDivisorTruncation D) e =
      (idealMoebius e : ℝ) := by
  apply collectedSieveCoefficient_eq_moebius _
    (fun c hc => ⟨(mem_squarefreeDivisorTruncation.mp hc).1,
      (mem_squarefreeDivisorTruncation.mp hc).2.1⟩) he hse
  intro c hc hsc hce
  exact mem_squarefreeDivisorTruncation.mpr ⟨hc,hsc,
    (norm_le_of_dvd_nonzero (primary_ne_zero he) hce).trans hD⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSquarefreeIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact square-divisor Möbius identity on primary elements.
This is the arithmetic inversion used by the low-height angular model. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_subset_square_dvd {a : Eisenstein} (ha : primary a)
    {s : Finset Eisenstein} (hs : s ⊆ primaryPrimeFactors a) :
    (∏ p ∈ s, p)^2 ∣ a ↔ ∀ p ∈ s, p^2 ∣ a := by
  constructor
  · intro h p hp
    exact (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp) 2).trans h
  · intro h
    rw [←Finset.prod_pow]
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      exact (primaryPrimes_isCoprime (primaryPrimeFactor_spec ha (hs hp)).1
        (primaryPrimeFactor_spec ha (hs hq)).1 hpq).pow
    · exact h

lemma primarySquarePrimeFactors_empty_iff {a : Eisenstein} (ha : primary a) :
    primarySquarePrimeFactors a = ∅ ↔ Squarefree a := by
  constructor
  · intro he
    by_contra hs
    obtain ⟨p,hp,hpa⟩ := exists_primary_prime_square_dvd ha hs
    have hd : p ∣ a := (dvd_mul_right p p).trans hpa
    have hm : p ∈ primarySquarePrimeFactors a := by
      exact Finset.mem_filter.mpr ⟨(primaryPrime_mem_factors_iff ha).mpr ⟨hp,hd⟩,
        by simpa only [pow_two] using hpa⟩
    simp only [he,Finset.notMem_empty] at hm
  · intro hs
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hh := Finset.mem_filter.mp hp
    have hu : IsUnit p := hs p (by simpa only [pow_two] using hh.2)
    exact (primaryPrimeFactor_spec ha hh.1).1.2.not_isUnit hu

lemma primary_square_divisors_image (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) {a : Eisenstein} (ha : primary a)
    (hcomplete : ∀ c, primary c → Squarefree c → c^2 ∣ a → c ∈ C) :
    C.filter (fun c => c^2 ∣ a) =
      (primarySquarePrimeFactors a).powerset.image (fun s => ∏ p ∈ s, p) := by
  ext c
  constructor
  · intro hc
    obtain ⟨hc,hd⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_image.mpr ⟨primaryPrimeFactors c,Finset.mem_powerset.mpr ?_,
      primaryPrimeFactors_prod (hC c hc).1 (hC c hc).2⟩
    intro p hp
    have hpc := (primaryPrimeFactor_spec (hC c hc).1 hp).2
    have hpa := (pow_dvd_pow_of_dvd hpc 2).trans hd
    exact Finset.mem_filter.mpr
      ⟨(primaryPrime_mem_factors_iff ha).mpr
        ⟨(primaryPrimeFactor_spec (hC c hc).1 hp).1,
          (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hpa⟩,hpa⟩
  · intro hc
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hc
    have hsub := Finset.mem_powerset.mp hs
    have hpr : ∀ p ∈ s, primaryPrime p := fun p hp =>
      (primaryPrimeFactor_spec ha (Finset.mem_filter.mp (hsub hp)).1).1
    have hprim := primary_finset_prod s (fun p : Eisenstein => p) (fun p hp => (hpr p hp).1)
    have hsq := primaryPrime_product_squarefree s hpr
    have hd : (∏ p ∈ s, p)^2 ∣ a :=
      (primary_subset_square_dvd ha (fun p hp => (Finset.mem_filter.mp (hsub hp)).1)).mpr
        (fun p hp => (Finset.mem_filter.mp (hsub hp)).2)
    exact Finset.mem_filter.mpr ⟨hcomplete _ hprim hsq hd,hd⟩

lemma sum_powerset_sign (P : Finset Eisenstein) :
    (∑ s ∈ P.powerset, (-1:ℝ)^s.card) = if P = ∅ then 1 else 0 := by
  have he := Finset.prod_add (fun _ : Eisenstein => (-1:ℝ)) (fun _ => (1:ℝ)) P
  simp only [Finset.prod_const_one,mul_one,Finset.prod_const,neg_add_cancel] at he
  rw [←he]
  by_cases hP : P = ∅
  · simp [hP]
  · simp [hP,Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hP)]

/-- Every square divisor is included, so the actual truncated coefficient
equals the squarefree indicator; no error term occurs. -/
theorem primary_square_moebius_inversion (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) {a : Eisenstein} (ha : primary a)
    (hcomplete : ∀ c, primary c → Squarefree c → c^2 ∣ a → c ∈ C) :
    (∑ c ∈ C, if c^2 ∣ a then (idealMoebius c:ℝ) else 0) =
      (idealMoebius a:ℝ)^2 := by
  rw [←Finset.sum_filter,primary_square_divisors_image C hC ha hcomplete]
  have hinj : Set.InjOn (fun s : Finset Eisenstein => ∏ p ∈ s, p)
      (↑(primarySquarePrimeFactors a).powerset : Set (Finset Eisenstein)) :=
    primaryPrimeFactors_prod_injective (fun p hp =>
      (primaryPrimeFactor_spec ha (Finset.mem_filter.mp hp).1).1)
  rw [Finset.sum_image hinj]
  have he : (∑ s ∈ (primarySquarePrimeFactors a).powerset,
      (idealMoebius (∏ p ∈ s, p):ℝ)) =
      ∑ s ∈ (primarySquarePrimeFactors a).powerset,(-1:ℝ)^s.card := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [idealMoebius_prod_primaryPrimes s (fun p hp =>
      (primaryPrimeFactor_spec ha (Finset.mem_filter.mp (Finset.mem_powerset.mp hs hp)).1).1)]
    push_cast
    rfl
  rw [he,sum_powerset_sign,idealMoebius_sq]
  simp only [primarySquarePrimeFactors_empty_iff ha]

lemma squarefreeDivisorTruncation_complete {a : Eisenstein} (ha : primary a)
    {X : ℝ} (hX : norm a ≤ X) {c : Eisenstein} (hc : primary c)
    (hsc : Squarefree c) (hd : c^2 ∣ a) :
    c ∈ squarefreeDivisorTruncation (Real.sqrt X) := by
  apply mem_squarefreeDivisorTruncation.mpr
  refine ⟨hc,hsc,Real.le_sqrt_of_sq_le ?_⟩
  have hn := (norm_le_of_dvd_nonzero (primary_ne_zero ha) hd).trans hX
  simpa only [pow_two,norm_mul_eq] using hn

theorem primary_square_moebius_truncation {a : Eisenstein} (ha : primary a)
    {X : ℝ} (hX : norm a ≤ X) :
    (∑ c ∈ squarefreeDivisorTruncation (Real.sqrt X),
      if c^2 ∣ a then (idealMoebius c:ℝ) else 0) = (idealMoebius a:ℝ)^2 := by
  exact primary_square_moebius_inversion _
    (fun c hc => ⟨(mem_squarefreeDivisorTruncation.mp hc).1,
      (mem_squarefreeDivisorTruncation.mp hc).2.1⟩) ha
    (fun c hc hs hd => squarefreeDivisorTruncation_complete ha hX hc hs hd)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSquarefreeLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-height angular cancellation for the literal squarefree,
coprime primary lattice sum. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coprimeAngularLattice_divisor (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (Y : ℝ) {d : Eisenstein} (hd : primary d) :
    (∑' u : Eisenstein, if primary u ∧ d ∣ u ∧ IsCoprime r u then
      theta ℓ u*W (norm u/Y) else 0) =
      if IsCoprime r d then theta ℓ d*primaryCoprimeAngularLattice r ℓ W (Y/norm d)
      else 0 := by
  have he (u : Eisenstein) :
      (if primary u ∧ d ∣ u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0) =
      if primary u ∧ d ∣ u then
        (if IsCoprime r u then theta ℓ u*W (norm u/Y) else 0) else 0 := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [tsum_primary_dvd_eq_multiples hd]
  by_cases hc : IsCoprime r d
  · rw [ite_eq_left hc,primaryCoprimeAngularLattice,←tsum_mul_left]
    apply tsum_congr
    intro u
    have hn : norm d ≠ 0 := ne_of_gt (norm_pos_of_ne_zero (primary_ne_zero hd))
    have hs : norm d*norm u/Y = norm u/(Y/norm d) := by field_simp
    simp only [IsCoprime.mul_right_iff,hc,true_and]
    by_cases hu : primary u <;> by_cases hru : IsCoprime r u <;>
      simp [hu,hru,theta_mul,norm_mul_eq,hs,mul_assoc]
  · rw [ite_eq_right hc]
    simp only [IsCoprime.mul_right_iff,hc,false_and,ite_false, if_false]
    simp

private lemma squarefreeAngular_pointwise_inversion (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) {Y S : ℝ} (hY : 0 < Y)
    (hcut : ∀ x : ℝ, S < x → W x = 0) (u : Eisenstein) :
    (if primary u ∧ IsCoprime r u then (idealMoebius u:ℂ)^2*theta ℓ u*W (norm u/Y) else 0) =
      ∑ c ∈ squarefreeDivisorTruncation (Real.sqrt (S*Y)),
        (idealMoebius c:ℂ)*
          (if primary u ∧ c^2 ∣ u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0) := by
  by_cases hu : primary u
  · by_cases hc : IsCoprime r u
    · by_cases hw : W (norm u/Y) = 0
      · simp [hw]
      · have hn : norm u ≤ S*Y := by
          have hh : norm u/Y ≤ S := le_of_not_gt (fun hh => hw (hcut _ hh))
          exact (div_le_iff₀ hY).mp hh
        have hi : (∑ c ∈ squarefreeDivisorTruncation (Real.sqrt (S*Y)),
            if c^2 ∣ u then (idealMoebius c:ℂ) else 0) = (idealMoebius u:ℂ)^2 := by
          exact_mod_cast primary_square_moebius_truncation hu hn
        rw [ite_eq_left ⟨hu,hc⟩,←hi,Finset.sum_mul,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c hc'
        by_cases hd : c^2 ∣ u <;> simp [hu,hc,hd,mul_assoc]
    · simp [hu,hc]
  · simp [hu]

private lemma squarefreeAngular_summable (r c : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hsm : ContDiff ℝ ∞ W)
    {Y : ℝ} (hY : 0 < Y) :
    Summable (fun u : Eisenstein => (idealMoebius c:ℂ)*
      (if primary u ∧ c^2 ∣ u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0)) := by
  have hs := summable_primary_angular_restricted ℓ W hW hsm hY
    (fun u => c^2 ∣ u ∧ IsCoprime r u)
  apply (hs.mul_left (idealMoebius c:ℂ)).congr
  intro u
  by_cases hu : primary u ∧ c^2 ∣ u ∧ IsCoprime r u
  · simp only [hu]
  · simp only [hu,ite_false, if_false]

theorem squarefreeCoprimeAngularLattice_expansion
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hsm : ContDiff ℝ ∞ W)
    {Y S : ℝ} (hY : 0 < Y)
    (hcut : ∀ x : ℝ, S < x → W x = 0) :
    squarefreeCoprimeAngularLattice r ℓ W Y =
      ∑ c ∈ squarefreeDivisorTruncation (Real.sqrt (S*Y)),
        (idealMoebius c:ℂ)*
          (if IsCoprime r (c^2) then theta ℓ (c^2)*
            primaryCoprimeAngularLattice r ℓ W (Y/norm (c^2)) else 0) := by
  let C := squarefreeDivisorTruncation (Real.sqrt (S*Y))
  let T (c u : Eisenstein) : ℂ := (idealMoebius c:ℂ)*
    (if primary u ∧ c^2 ∣ u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0)
  have hsum (c : Eisenstein) : Summable (T c) := squarefreeAngular_summable r c ℓ W hW hsm hY
  have he (u : Eisenstein) :
      (if primary u ∧ IsCoprime r u then (idealMoebius u:ℂ)^2*theta ℓ u*W (norm u/Y) else 0) =
        ∑ c ∈ C,T c u := squarefreeAngular_pointwise_inversion r ℓ W hY hcut u
  unfold squarefreeCoprimeAngularLattice
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun c _ => hsum c)]
  apply Finset.sum_congr rfl
  intro c hc
  have hprim : primary (c^2) := by
    simpa only [pow_two] using primary_mul (mem_squarefreeDivisorTruncation.mp hc).1
      (mem_squarefreeDivisorTruncation.mp hc).1
  change (∑' u : Eisenstein,(idealMoebius c:ℂ)*_) = _
  rw [tsum_mul_left,coprimeAngularLattice_divisor r ℓ W Y hprim]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularWeightOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed continuous operator from logarithmic test functions to plane
annuli. It makes the angular lattice bounds uniform over the given weights. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology SchwartzMap
namespace CubicFirstMoment

lemma angularComplexCutoff_compact {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasCompactSupport (angularComplexCutoff a b) :=
  (angularPositiveCutoff_compact ha hb).comp_left Complex.ofReal_zero

lemma angularComplexCutoff_smooth (a b : ℝ) :
    ContDiff ℝ ∞ (angularComplexCutoff a b) :=
  Complex.ofRealCLM.contDiff.comp (angularPositiveCutoff_smooth a b)

lemma angularComplexCutoff_positive {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    tsupport (angularComplexCutoff a b) ⊆ Ioi 0 := by
  have he : Function.support (angularComplexCutoff a b) =
      Function.support (angularPositiveCutoff a b) := by
    ext x
    simp only [Function.mem_support,angularComplexCutoff,ne_eq,Complex.ofReal_eq_zero]
  change closure (Function.support _) ⊆ _
  rw [he]
  exact angularPositiveCutoff_positive ha hb

lemma angularWeightOperator_apply (ℓ : ℤ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (F : 𝓢(ℝ,ℂ)) (z : ℂ) :
    angularWeightOperator ℓ a b ha hb F z =
      angularAnnulus ℓ (angularComplexCutoff a b) z *
        F (angularLogExtension (a/2) (2*b) (Complex.normSq z)) := by
  have hq := (angularAnnulus_compact ℓ (angularComplexCutoff_compact ha hb)).hasTemperateGrowth
    (angularAnnulus_smooth ℓ (angularComplexCutoff_positive ha hb) (angularComplexCutoff_smooth a b))
  change (SchwartzMap.smulLeftCLM ℂ (angularAnnulus ℓ (angularComplexCutoff a b))) _ z = _
  rw [SchwartzMap.smulLeftCLM_apply_apply hq]
  rfl

lemma angularWeightOperator_log_apply (ℓ : ℤ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (hsupp : tsupport W ⊆ Icc a b) :
    angularWeightOperator ℓ a b ha hb (mellinLogSchwartz W hW hpos hsm 0) =
      angularAnnulusSchwartz ℓ W hW hpos hsm := by
  ext z
  rw [angularWeightOperator_apply]
  let x := Complex.normSq z
  by_cases hk : angularPositiveCutoff a b x = 0
  · have hw : W x = 0 := by
      by_contra hn
      have hix := hsupp (subset_tsupport _ hn)
      have ho := angularPositiveCutoff_one ha hb hix
      exact zero_ne_one (hk.symm.trans ho)
    change (angularPlanePhase ℓ z*(angularPositiveCutoff a b x:ℂ))*
      mellinLogSchwartz W hW hpos hsm 0 (angularLogExtension (a/2) (2*b) x) =
        angularPlanePhase ℓ z*W x
    simp only [hk,Complex.ofReal_zero,mul_zero,zero_mul,hw]
  · have hx := angularPositiveCutoff_tsupport ha hb (subset_tsupport _ hk)
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
    have hg := angularLogExtension_eq_log (by positivity : 0 < a/2)
      (by positivity : 0 < 2*b) hx
    have hc : (angularPositiveCutoff a b x:ℂ)*W x = W x := by
      by_cases hw : W x = 0
      · simp only [hw,mul_zero]
      · rw [angularPositiveCutoff_one ha hb (hsupp (subset_tsupport _ hw)),
          Complex.ofReal_one,one_mul]
    change (angularPlanePhase ℓ z*(angularPositiveCutoff a b x:ℂ))*
      mellinLogSchwartz W hW hpos hsm 0 (angularLogExtension (a/2) (2*b) x) =
        angularPlanePhase ℓ z*W x
    rw [hg]
    simp only [mellinLogSchwartz_apply,neg_zero,zero_mul,Real.exp_zero,one_smul,neg_neg,Real.exp_log hx0]
    rw [mul_assoc,hc]

theorem UniformLogWeights.angularAnnulus_bounded {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (ℓ : ℤ) :
    Bornology.IsVonNBounded ℝ
      ((fun i => angularAnnulusSchwartz ℓ (W i) (h.compact i) (h.positive i) (h.smooth i)) '' Set.univ) := by
  let f : ι → 𝓢(ℝ,ℂ) := fun i => mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) 0
  have hb : Bornology.IsVonNBounded ℝ (f '' Set.univ) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro kn
    obtain ⟨C,hC,hbound⟩ := h.log_seminorms 0 kn.1 kn.2
    refine ⟨C+1,by linarith,?_⟩
    intro i _
    exact (hbound i 0 (by simp)).trans_lt (by linarith)
  let L := angularWeightOperator ℓ (Real.exp (-h.radius)) (Real.exp h.radius)
    (Real.exp_pos _) (Real.exp_pos _)
  have he : L '' (f '' Set.univ) =
      ((fun i => angularAnnulusSchwartz ℓ (W i) (h.compact i) (h.positive i) (h.smooth i)) '' Set.univ) := by
    rw [←Set.image_comp]
    congr 1
    funext i
    exact angularWeightOperator_log_apply ℓ (Real.exp_pos _) (Real.exp_pos _)
      (W i) (h.compact i) (h.positive i) (h.smooth i) (h.annular_support i)
  rw [←he]
  exact hb.image L

theorem UniformLogWeights.angularFourier_seminorm {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (ℓ : ℤ) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i,
      SchwartzMap.seminorm ℝ k n (traceFourierSchwartz
        (angularAnnulusSchwartz ℓ (W i) (h.compact i) (h.positive i) (h.smooth i))) ≤ C := by
  let f : ι → 𝓢(ℂ,ℂ) := fun i =>
    angularAnnulusSchwartz ℓ (W i) (h.compact i) (h.positive i) (h.smooth i)
  have hb := (h.angularAnnulus_bounded ℓ).image angularTraceFourierCLM
  rw [←Set.image_comp] at hb
  obtain ⟨C,hC,hbound⟩ :=
    (schwartz_withSeminorms ℝ ℂ ℂ).image_isVonNBounded_iff_seminorm_bounded
      (angularTraceFourierCLM ∘ f) |>.mp hb (k,n)
  exact ⟨C,hC,fun i => (hbound i (Set.mem_univ i)).le⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularUniformPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-area coset estimate with a constant chosen before the weight.
The common Fourier decay is derived by the continuous operator. -/
noncomputable section
open MeasureTheory
open scoped BigOperators SchwartzMap
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem schwartz_weighted_dual_bound (F : 𝓢(ℂ,ℂ)) {D : ℝ} (hD : 0 ≤ D)
    (hdecay : ∀ z : ℂ, ‖z‖^4*‖traceFourier F z‖ ≤ D)
    (w : ℂ) (hw : w ≠ 0) (c : Eisenstein → ℂ) (hc : ∀ h, ‖c h‖ ≤ 1) :
    ‖∑' h : Eisenstein, if h = 0 then 0 else c h*traceFourier F ((h:ℂ)/w)‖ ≤
      (D*(∑' h : Eisenstein, (norm h)^(-(2:ℝ)))+1)*(Complex.normSq w)^2 := by
  have hwN : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have hs : Summable (fun h : Eisenstein => if h = 0 then (0:ℂ) else
      c h*traceFourier F ((h:ℂ)/w)) := by
    apply (traceFourier_summable_eisenstein F w hw).norm.of_norm_bounded
    intro h
    by_cases hh : h = 0
    · simp only [hh,ite_true, if_true,norm_zero]
      exact _root_.norm_nonneg _
    · simp only [hh,ite_false, if_false,norm_mul]
      exact mul_le_of_le_one_left (_root_.norm_nonneg _) (hc h)
  have hbound (h : Eisenstein) :
      ‖if h = 0 then (0:ℂ) else c h*traceFourier F ((h:ℂ)/w)‖ ≤
        D*(Complex.normSq w)^2*(norm h)^(-(2:ℝ)) := by
    by_cases hh : h = 0
    · simp only [ite_eq_left hh,norm_zero]
      exact mul_nonneg (mul_nonneg hD (sq_nonneg _)) (Real.rpow_nonneg (norm_nonneg h) _)
    · rw [ite_eq_right hh,norm_mul]
      apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (hc h)).trans
      have hn : 0 < norm h := norm_pos_of_ne_zero hh
      have he : ‖(h:ℂ)/w‖^4 = (norm h)^2/(Complex.normSq w)^2 := by
        rw [show (4:ℕ) = 2*2 by norm_num,pow_mul,←Complex.normSq_eq_norm_sq,
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
    _ ≤ ∑' h : Eisenstein, ‖if h = 0 then (0:ℂ) else c h*traceFourier F ((h:ℂ)/w)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' h : Eisenstein, D*(Complex.normSq w)^2*(norm h)^(-(2:ℝ)) :=
      Summable.tsum_le_tsum hbound hs.norm
        ((summable_eisenstein_norm_rpow (s := 2) (by norm_num)).mul_left _)
    _ = D*(∑' h : Eisenstein, (norm h)^(-(2:ℝ)))*(Complex.normSq w)^2 := by
      rw [tsum_mul_left]
      ring
    _ ≤ _ := by nlinarith [sq_nonneg (Complex.normSq w)]

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma idealMoebius_sq_mul_of_squarefree {r : Eisenstein} (hr : Squarefree r)
    (u : Eisenstein) :
    (idealMoebius (r*u):ℂ)^2 = if IsCoprime r u then (idealMoebius u:ℂ)^2 else 0 := by
  simp only [idealMoebius_sq_complex,squarefree_mul_iff,isRelPrime_iff_isCoprime,hr]
  split_ifs <;> simp_all

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedUniform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeBinGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GeometricPrimeBins
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeExclusionLog
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBinMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelPartialSummation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimeUpper
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothRankinSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_QuantitativeNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCharacterRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem stopped_interval_energy {ξ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (W : ι → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (selected : Eisenstein → Eisenstein → Prop) (u a b : ℝ) (e : Eisenstein),
      0 ≤ b → b ≤ X →
      (∀ n ∈ stoppedIntervalSupport ι X a b e,
        ‖stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n‖ ≤ M) ∧
      (∑ n ∈ stoppedIntervalSupport ι X a b e,
        ‖stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n‖^2) ≤ 18*b*M^2 := by
  obtain ⟨M,hM,hbound⟩ := stoppedBeta_distinguished_uniform (ι := ι) hξ hξz
    (C := 1) (by norm_num)
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
    (fun _ _ hx => primeDetectorCutoff_one hx)
    (fun _ hx => primeDetectorCutoff_zero hx)
  refine ⟨M,hM,?_⟩
  filter_upwards [hbound] with X hbound
  intro W hW selected u a b e hb hbX
  have hrow (n : Eisenstein) (hn : n ∈ stoppedIntervalSupport ι X a b e) :
      ‖stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n‖ ≤ M := by
    obtain ⟨hnp,hns,hnB⟩ := stoppedIntervalSupport_spec X a b e hn
    unfold stoppedRowCoefficient
    rw [norm_mul,norm_normTwist,mul_one]
    apply hbound (fun _ : ι => primeCutoff X) (fun i p => W i (norm p))
      (orderedConvolutionSupport (fun _ : ι => primeCutoff X)) (primaryElementBall X)
      selected (fun _ _ hp => (mem_primeCutoff.mp hp).1) (fun i p _ => hW i (norm p))
      (fun r hr => orderedPrimarySupport_primary _
        (fun _ _ hp => (mem_primeCutoff.mp hp).1.1) hr) n hnp hns
    simpa only [one_mul] using hnB.trans hbX
  refine ⟨hrow,?_⟩
  have hcard := primary_support_card_le (stoppedIntervalSupport ι X a b e) hb
    (fun n hn => ⟨(stoppedIntervalSupport_spec X a b e hn).1,
      (stoppedIntervalSupport_spec X a b e hn).2.2⟩)
  calc
    _ ≤ ∑ _n ∈ stoppedIntervalSupport ι X a b e, M^2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (_root_.norm_nonneg _) (hrow n hn) 2
    _ = ((stoppedIntervalSupport ι X a b e).card:ℝ)*M^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg M)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedMellinRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two actual coprime Poisson rows are the literal stopped rows at
the shifted norm heights. Divisibility filters and the original interval
support remain in the statement. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedRowCoefficient_phase (X w z u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (n : Eisenstein) :
    stoppedRowCoefficient X w z u W selected n =
      stoppedRowCoefficient X w z 0 W selected n*mellinPhase u (norm n) := by
  have hz : mellinPhase 0 (norm n) = 1 := by simp [mellinPhase]
  simp only [stoppedRowCoefficient,normTwist_eq_mellinPhase,hz,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedRoughSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-factor roughness of the actual stopped coefficient. The selected
factor is rough because its bins precede the stopping bin; the distinguished
factor is rough because its coefficient vanishes at small primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma geometricBinLower_antitone {ρ X : ℝ} (hρ : 1 ≤ ρ) :
    Antitone (geometricBinLower ρ X) := by
  intro i j hij
  exact pow_le_pow_right₀ hρ (Nat.sub_le_sub_left hij _)

theorem stoppingSideTest_prime_roughness {ρ X Z : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j k : ℕ} {r d p : Eisenstein} (hd : primary d) (hdX : norm d ≤ X)
    (hs : stoppingSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k Z r d)
    (hp : primaryPrime p) (hpd : p ∣ d) :
    geometricBinLower ρ X j ≤ norm p := by
  have hmem := (primaryPrime_mem_factors_iff hd).mpr ⟨hp,hpd⟩
  have hbin := hs.1 p hmem
  have hpX := (norm_le_of_dvd (primary_ne_zero hd) hpd).trans hdX
  exact (geometricBinLower_antitone hρ.le hbin).trans
    (geometricPrimeBin_cell hρ hρ₂ hp hpX).1

theorem stoppedBeta_prime_roughness
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) (R D : Finset Eisenstein)
    {ψ : ℝ → ℝ} (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z ρ X Z Q : ℝ} (hw : 0 < w) (hwz : w ≤ z)
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hD : ∀ d ∈ D, primary d ∧ norm d ≤ X)
    (j k h : ℕ) (early : Bool) {b p : Eisenstein}
    (hb : stoppedBeta R D (distinguishedTupleCoefficient S W ψ w z) ψ w
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
        j k h Z Q early) b ≠ 0)
    (hp : primaryPrime p) (hpb : p ∣ b) :
    min w (geometricBinLower ρ X j) ≤ norm p := by
  unfold stoppedBeta primaryPairCoefficient at hb
  obtain ⟨q,hq,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  obtain ⟨hq,hprod⟩ := Finset.mem_filter.mp hq
  obtain ⟨_hr,hd⟩ := Finset.mem_product.mp hq
  have hsel : stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h Z Q early q.1 q.2 := by
    by_contra hn
    exact hterm (ite_eq_right hn)
  rw [ite_eq_left hsel] at hterm
  have hv := (mul_ne_zero_iff.mp hterm).1
  have hdiv : p ∣ q.1*q.2 := by rwa [hprod]
  rcases hp.2.dvd_mul.mp hdiv with hpr | hpd
  · exact (min_le_left _ _).trans
      (distinguishedTupleCoefficient_prime_support S hS W hψone hψzero
        hw hwz hv hp hpr).1.le
  · exact (min_le_right _ _).trans
      (stoppingSideTest_prime_roughness hρ hρ₂ (hD q.2 hd).1 (hD q.2 hd).2
        hsel.1 hp hpd)

theorem stoppedBeta_early_prime_roughness
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) (R D : Finset Eisenstein)
    {ψ : ℝ → ℝ} (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z ρ X Z Q : ℝ} (hw : 0 < w) (hwz : w ≤ z)
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hD : ∀ d ∈ D, primary d ∧ norm d ≤ X)
    (j k h : ℕ) (early : Bool) (hj : j ≤ h) {b p : Eisenstein}
    (hb : stoppedBeta R D (distinguishedTupleCoefficient S W ψ w z) ψ w
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
        j k h Z Q early) b ≠ 0)
    (hp : primaryPrime p) (hpb : p ∣ b) :
    min w (geometricBinLower ρ X h) ≤ norm p := by
  exact (min_le_min_left w (geometricBinLower_antitone hρ.le hj)).trans
    (stoppedBeta_prime_roughness S hS W R D hψone hψzero hw hwz hρ hρ₂ hD
      j k h early hb hp hpb)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedRoughRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Early stopping makes every nonempty small-divisor row identically
zero. The cutoff is the actual minimum of the distinguished-prime cutoff
and the final permitted stopping-bin endpoint. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedRowCoefficient_early_roughness
    (X w z u ρ Z Q : ℝ) (W : ι → ℝ → ℂ)
    (hw : 0 < w) (hwz : w ≤ z) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (j k h : ℕ) (early : Bool) (hj : j ≤ h) {n p : Eisenstein}
    (hn : stoppedRowCoefficient X w z u W
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
        j k h Z Q early) n ≠ 0)
    (hp : primaryPrime p) (hpn : p ∣ n) :
    min w (geometricBinLower ρ X h) ≤ norm p := by
  have hb := (mul_ne_zero_iff.mp hn).1
  exact stoppedBeta_early_prime_roughness (fun _ : ι => primeCutoff X)
    (fun _ _ hp => (mem_primeCutoff.mp hp).1) (fun i p => W i (norm p))
    (orderedConvolutionSupport (fun _ : ι => primeCutoff X)) (primaryElementBall X)
    (fun _ _ hx => primeDetectorCutoff_one hx)
    (fun _ hx => primeDetectorCutoff_zero hx) hw hwz hρ hρ₂
    (fun _ hd => mem_primaryElementBall.mp hd) j k h early hj hb hp hpn

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCubeRoughness
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual early-stopped row has a logarithmic reciprocal-prime
exclusion bound. Zero coefficients are kept explicit rather than requiring
roughness of an artificial ambient support. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_prime_factors_card_log {a : Eisenstein} (ha : primary a) :
    ((primaryPrimeFactors a).card:ℝ) ≤ Real.log (norm a)/Real.log 2 := by
  have hh := primary_prime_divisor_card_log (primaryPrimeFactors a)
    (fun p hp => (primaryPrimeFactor_spec ha hp).1) a (primary_ne_zero ha)
  have he : (primaryPrimeFactors a).filter (fun p => p ∣ a) = primaryPrimeFactors a :=
    Finset.filter_eq_self.mpr (fun p hp => (primaryPrimeFactor_spec ha hp).2)
  rwa [he] at hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedModelNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The model polynomial of a bounded stopped row has the expected
b^(5/6) size, directly from its literal norm support. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma bounded_annular_model_norm (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M)
    (hS : ∀ a ∈ S, primary a ∧ b/2 ≤ norm a ∧ norm a ≤ b)
    (hβ : ∀ a ∈ S, ‖β a‖ ≤ M) (u : ℝ) :
    ‖dispersionModel S β u‖ ≤ (18*(2:ℝ)^(1/6:ℝ)*M)*b^(5/6:ℝ) := by
  have hrow (a : Eisenstein) (ha : a ∈ S) :
      ‖β a*normTwist u a*((norm a^(-1/6:ℝ):ℝ):ℂ)‖ ≤ M*(b/2)^(-1/6:ℝ) := by
    rw [norm_mul,norm_mul,norm_normTwist,mul_one,Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg a) _)]
    exact mul_le_mul (hβ a ha)
      (Real.rpow_le_rpow_of_nonpos (by positivity) (hS a ha).2.1 (by norm_num))
      (Real.rpow_nonneg (norm_nonneg a) _) hM
  have hpow : b*(b/2)^(-1/6:ℝ) = (2:ℝ)^(1/6:ℝ)*b^(5/6:ℝ) := by
    rw [Real.div_rpow hb.le (by norm_num),div_eq_mul_inv,
      ←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    norm_num only [neg_div,neg_neg]
    calc
      _ = (2:ℝ)^(1/6:ℝ)*(b^(1:ℝ)*b^(-1/6:ℝ)) := by rw [Real.rpow_one]; ring_nf
      _ = _ := by rw [←Real.rpow_add hb]; norm_num
  apply (norm_sum_le S (fun a => β a*normTwist u a*((norm a^(-1/6:ℝ):ℝ):ℂ))).trans
  calc
    _ ≤ ∑ _a ∈ S, M*(b/2)^(-1/6:ℝ) := Finset.sum_le_sum hrow
    _ = (S.card:ℝ)*(M*(b/2)^(-1/6:ℝ)) := by simp
    _ ≤ (18*b)*(M*(b/2)^(-1/6:ℝ)) := mul_le_mul_of_nonneg_right
      (primary_support_card_le S hb.le (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩))
      (by positivity)
    _ = (18*M)*(b*(b/2)^(-1/6:ℝ)) := by ring
    _ = _ := by rw [hpow]; ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_model_norm {ξ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (W : ι → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein) (b u v : ℝ),
      0 < b → b ≤ X →
      ‖dispersionModel (stoppedIntervalSupport ι X (b/2) b e)
        (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected) v‖ ≤ K*b^(5/6:ℝ) := by
  obtain ⟨M,hM,hbound⟩ := stopped_interval_energy (ι := ι) hξ hξz
  refine ⟨18*(2:ℝ)^(1/6:ℝ)*M,by positivity,?_⟩
  filter_upwards [hbound] with X hbound
  intro W hW selected e b u v hb hbX
  apply bounded_annular_model_norm _ _ hb hM.le
  · intro a ha
    have hs := stoppedIntervalSupport_spec X (b/2) b e ha
    exact ⟨hs.1,(Finset.mem_filter.mp ha).2.2.2.1.le,hs.2.2⟩
  · exact (hbound W hW selected u (b/2) b e hb.le hbX).1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeExclusions
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelOverlapCounting
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma noncoprime_row_card_le (S : Finset Eisenstein) {Y D : ℝ}
    (hY : 0 ≤ Y) (hD : 0 < D) (hS : ∀ b ∈ S, b ≠ 0 ∧ norm b ≤ Y)
    {a : Eisenstein} (ha : primary a) (hsa : Squarefree a)
    (hrough : ∀ p ∈ primaryPrimeFactors a, D ≤ norm p) :
    ((S.filter (fun b => ¬IsCoprime a b)).card:ℝ) ≤
      (primaryPrimeFactors a).card*(18*Y/D) := by
  have hs : S.filter (fun b => ¬IsCoprime a b) ⊆
      (primaryPrimeFactors a).biUnion (fun p => S.filter (fun b => p ∣ b)) := by
    intro b hb
    obtain ⟨hb,hcop⟩ := Finset.mem_filter.mp hb
    obtain ⟨p,hp,hpb⟩ := not_coprime_prime_cover ha hsa hcop
    exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨hb,hpb⟩⟩
  calc
    _ ≤ ∑ p ∈ primaryPrimeFactors a, ((S.filter (fun b => p ∣ b)).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hs).trans (Finset.card_biUnion_le)
    _ ≤ ∑ _p ∈ primaryPrimeFactors a, 18*Y/D := by
      apply Finset.sum_le_sum
      intro p hp
      exact (divisible_row_card_le S hY hS p (primaryPrimeFactor_spec ha hp).1.2.ne_zero).trans
        (div_le_div_of_nonneg_left (by positivity) hD (hrough p hp))
    _ = _ := by simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RadialCubing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three-to-one cubing Jacobian in the radial integral. -/

noncomputable section
open scoped BigOperators
open MeasureTheory MeasureTheory.Measure Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma complex_radial_integral (φ : ℝ → ℂ) :
    (∫ z : ℂ, φ ‖z‖) = (2*Real.pi:ℂ)*(∫ r in Ioi (0:ℝ), (r:ℂ)*φ r) := by
  calc
    _ = ∫ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, (p.1:ℂ)*φ |p.1| := by
      rw [← Complex.integral_comp_polarCoord_symm,polarCoord_target]
      simp only [Complex.norm_polarCoord_symm,Complex.real_smul]
    _ = (∫ r in Ioi (0:ℝ), (r:ℂ)*φ |r|)*(∫ _ in Ioo (-Real.pi) Real.pi, (1:ℂ)) := by
      rw [← setIntegral_prod_mul,volume_eq_prod]
      simp only [mul_one]
    _ = (2*Real.pi:ℂ)*(∫ r in Ioi (0:ℝ), (r:ℂ)*φ r) := by
      have hφ : (∫ r in Ioi (0:ℝ), (r:ℂ)*φ |r|) = ∫ r in Ioi (0:ℝ), (r:ℂ)*φ r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        change (r:ℂ)*φ |r| = (r:ℂ)*φ r
        rw [abs_of_pos hr]
      rw [hφ]
      simp only [integral_const,measureReal_restrict_apply MeasurableSet.univ,
        Set.univ_inter,Complex.real_smul,mul_one]
      rw [Real.volume_real_Ioo_of_le (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos])]
      push_cast
      ring

lemma radial_cubing_integral (φ : ℝ → ℂ) :
    (∫ z : ℂ, φ (‖z‖^3)) = (1/3:ℂ)*
      (∫ z : ℂ, ((‖z‖^(-(4/3:ℝ)):ℝ):ℂ)*φ ‖z‖) := by
  rw [complex_radial_integral (fun r => φ (r^3)),
    complex_radial_integral (fun r => ((r^(-(4/3:ℝ)):ℝ):ℂ)*φ r)]
  have hsub := integral_comp_rpow_Ioi (fun r : ℝ => ((r^(-(1/3:ℝ)):ℝ):ℂ)*φ r)
    (show (3:ℝ) ≠ 0 by norm_num)
  have hp (r : ℝ) (hr : r ∈ Ioi (0:ℝ)) :
      (abs (3:ℝ)*r^((3:ℝ)-1)) • (((((r^(3:ℝ))^(-(1/3:ℝ))):ℝ):ℂ)*φ (r^(3:ℝ))) =
        (3:ℂ)*((r:ℂ)*φ (r^3)) := by
    have hrr : (r^(3:ℝ))^(-(1/3:ℝ)) = r⁻¹ := by
      rw [← Real.rpow_mul hr.le]
      norm_num [Real.rpow_neg_one]
    rw [hrr,Real.rpow_ofNat]
    norm_num
    have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    field_simp
  have hsub' : (3:ℂ)*(∫ r in Ioi (0:ℝ), (r:ℂ)*φ (r^3)) =
      ∫ r in Ioi (0:ℝ), ((r^(-(1/3:ℝ)):ℝ):ℂ)*φ r := by
    rw [← integral_const_mul]
    rw [← hsub]
    exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => (hp r hr).symm)
  have hweight : (∫ r in Ioi (0:ℝ), (r:ℂ)*(((r^(-(4/3:ℝ)):ℝ):ℂ)*φ r)) =
      ∫ r in Ioi (0:ℝ), ((r^(-(1/3:ℝ)):ℝ):ℂ)*φ r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have he : r*r^(-(4/3:ℝ)) = r^(-(1/3:ℝ)) := by
      nth_rw 1 [← Real.rpow_one r]
      rw [← Real.rpow_add hr]
      norm_num
    dsimp only
    rw [← mul_assoc,← Complex.ofReal_mul,he]
  rw [hweight,← hsub']
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RieszConstant
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact numerical constant in the cubic Riesz integral. -/

noncomputable section
namespace CubicFirstMoment

lemma Gamma_third_mul_two_thirds :
    Real.Gamma (1/3:ℝ)*Real.Gamma (2/3:ℝ) = 2*Real.pi/Real.sqrt 3 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1/3:ℝ)
  norm_num at h
  rw [show Real.pi*(1/3:ℝ) = Real.pi/3 by ring,Real.sin_pi_div_three] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma cStar_sq : cStar^2 =
    (2*Real.pi)^(4/3:ℝ)/(9*(Real.Gamma (2/3:ℝ))^2) := by
  unfold cStar
  rw [div_pow,mul_pow,← Real.rpow_natCast ((2*Real.pi)^(2/3:ℝ)) 2,
    ← Real.rpow_mul (by positivity : 0 ≤ 2*Real.pi)]
  norm_num

/-- Includes the cubing multiplicity, trace-pairing dilation, and the
covolume-normalized planar measure. -/
theorem cubic_riesz_constant :
    (1/3:ℝ)*(2/Real.sqrt 3)*Real.pi*(2*Real.pi)^(-(2/3:ℝ))*
      Real.Gamma (1/3:ℝ)/Real.Gamma (2/3:ℝ) = cStar^2 := by
  have hg : Real.Gamma (2/3:ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hs : Real.sqrt (3:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hh : Real.Gamma (1/3:ℝ) =
      (2*Real.pi)/(Real.sqrt 3*Real.Gamma (2/3:ℝ)) := by
    apply (eq_div_iff (mul_ne_zero hs hg)).mpr
    have h := Gamma_third_mul_two_thirds
    apply (eq_div_iff hs).mp at h
    nlinarith [h]
  rw [hh,cStar_sq]
  have hr : (2*Real.pi)^2*(2*Real.pi)^(-(2/3:ℝ)) = (2*Real.pi)^(4/3:ℝ) := by
    rw [← Real.rpow_natCast (2*Real.pi) 2,← Real.rpow_add (by positivity : 0 < 2*Real.pi)]
    norm_num
  rw [← hr]
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

lemma cubic_riesz_gaussian_constant :
    (1/3:ℝ)*(2/Real.sqrt 3)*Real.pi*(4*Real.pi^2)^(-(1/3:ℝ))*
      Real.Gamma (1/3:ℝ)/Real.Gamma (2/3:ℝ) = cStar^2 := by
  have he : (4*Real.pi^2)^(-(1/3:ℝ)) = (2*Real.pi)^(-(2/3:ℝ)) := by
    rw [show 4*Real.pi^2 = (2*Real.pi)^2 by ring,
      ← Real.rpow_natCast (2*Real.pi) 2,← Real.rpow_mul (by positivity : 0 ≤ 2*Real.pi)]
    norm_num
  rw [he]
  exact cubic_riesz_constant

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TraceDuality
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral self-duality for the symmetric Eisenstein trace pairing. -/

noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma integral_traceFourier_mul (f g : ℂ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ y : ℂ, traceFourier f y*g y) = ∫ x : ℂ, f x*traceFourier g x := by
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (L := traceBilinear) (ContinuousLinearMap.mul ℂ ℂ)
    Real.continuous_fourierChar
    (by change Continuous (fun p : ℂ × ℂ => 2*(p.1*p.2).re); fun_prop) hf hg
  have hflip (x y : ℂ) : traceBilinear.flip x y = tracePair x y := by
    change tracePair y x = tracePair x y
    simp only [tracePair,mul_comm]
  have hpair (x y : ℂ) : traceBilinear x y = tracePair x y := rfl
  simpa only [VectorFourier.fourierIntegral,hpair,hflip,traceFourier,
    Circle.smul_def,smul_eq_mul,ContinuousLinearMap.mul_apply',LinearMap.coe_mk,AddHom.coe_mk]
    using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GaussianDuality
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian test-function identity used to evaluate the Riesz integral. -/

noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma integrable_trace_gaussian {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (t:ℂ)) (by simpa using ht) 0 0
  simpa using h

lemma integral_traceFourier_gaussian (f : ℂ → ℂ) (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) :
    (∫ y : ℂ, traceFourier f y*Complex.exp (-(t:ℂ)*‖y‖^2)) =
      (Real.pi/t:ℝ)*(∫ x : ℂ, f x*Complex.exp ((-4*Real.pi^2/t*Complex.normSq x:ℝ):ℂ)) := by
  rw [integral_traceFourier_mul f _ hf (integrable_trace_gaussian ht)]
  simp_rw [traceFourier_gaussian ht]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RieszIntegrability
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability of the two Riesz weights used in the cubic dispersion integral. -/

noncomputable section
open scoped SchwartzMap
open MeasureTheory Set Metric
namespace CubicFirstMoment

/-- The singularity is locally integrable in dimension two; away from
zero the weight is bounded and Schwartz integrability suffices. -/
theorem schwartz_riesz_integrable (F : 𝓢(ℂ,ℂ)) {a : ℝ} (ha : 0 < a) (ha2 : a < 2) :
    Integrable (fun z : ℂ => ((‖z‖^(-a):ℝ):ℂ)*F z) := by
  let g (z : ℂ) : ℂ := ((‖z‖^(-a):ℝ):ℂ)*F z
  have hm : AEStronglyMeasurable g volume := by
    dsimp only [g]
    exact ((Complex.continuous_ofReal.measurable.comp
      (measurable_norm.pow_const (-a))).mul F.continuous.measurable).aestronglyMeasurable
  obtain ⟨C,hC,hbound⟩ := F.decay 0 0
  simp only [pow_zero,one_mul,norm_iteratedFDeriv_zero] at hbound
  have hlocal : IntegrableOn g (ball (0:ℂ) 1) := by
    apply integrableOn_ball_of_norm_le_rpow (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (α := a) (C := C) (by simpa using ha2) _ hm
    filter_upwards with z
    dsimp only [g]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (_root_.norm_nonneg z) _)]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (hbound z) (Real.rpow_nonneg (_root_.norm_nonneg z) (-a))
  have hfar : IntegrableOn g (ball (0:ℂ) 1)ᶜ := by
    apply F.integrable.norm.restrict.mono' hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with z hz
    dsimp only [g]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (_root_.norm_nonneg z) _)]
    have hz1 : 1 ≤ ‖z‖ := by simpa only [Set.mem_compl_iff,mem_ball,dist_zero_right,not_lt] using hz
    have hw : ‖z‖^(-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz1 (neg_nonpos.mpr ha.le)
    exact mul_le_of_le_one_left (_root_.norm_nonneg _) hw
  have hwhole := hlocal.union hfar
  simpa only [union_compl_self,integrableOn_univ] using hwhole

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RieszFubini
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence for the Gaussian representation of the Riesz pairing. -/

noncomputable section
open scoped SchwartzMap
open MeasureTheory Set
namespace CubicFirstMoment

private lemma ae_complex_ne_zero : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
  rw [ae_iff]
  simp

lemma rieszGaussianWeight_integral {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z ≠ 0) :
    (∫ t in Ioi (0:ℝ), rieszGaussianWeight a z t) = Real.Gamma a*‖z‖^(-2*a) := by
  simp only [rieszGaussianWeight]
  rw [laplace_rpow ha (sq_pos_of_pos (norm_pos_iff.mpr hz))]
  congr 1
  rw [← Real.rpow_natCast ‖z‖ 2,← Real.rpow_mul (_root_.norm_nonneg z)]
  congr 1
  ring

lemma rieszGaussianWeight_nonneg (a : ℝ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    0 ≤ rieszGaussianWeight a z t :=
  mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _)

/-- Tonelli's integrability criterion makes the subsequent interchange
of the Gaussian and spatial integrals legitimate. -/
theorem integrable_riesz_gaussian_product (F : 𝓢(ℂ,ℂ)) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) :
    Integrable (fun p : ℂ × ℝ => (rieszGaussianWeight a p.1 p.2 : ℂ)*F p.1)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable
      (fun p : ℂ × ℝ => (rieszGaussianWeight a p.1 p.2 : ℂ)*F p.1)
      (volume.prod (volume.restrict (Ioi 0))) := by
    apply Measurable.aestronglyMeasurable
    unfold rieszGaussianWeight
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_complex_ne_zero] with z hz
    exact (integrable_laplace_rpow ha (sq_pos_of_pos (norm_pos_iff.mpr hz))).ofReal.mul_const (F z)
  · have hw : Integrable (fun z : ℂ => Real.Gamma a*(‖z‖^(-2*a)*‖F z‖)) := by
      have h := (schwartz_riesz_integrable F (mul_pos (by norm_num : (0:ℝ) < 2) ha)
        (by linarith : 2*a < 2)).norm.const_mul (Real.Gamma a)
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (_root_.norm_nonneg z) _)]
      simp only [neg_mul]
    apply hw.congr
    filter_upwards [ae_complex_ne_zero] with z hz
    calc
      _ = (∫ t in Ioi (0:ℝ), rieszGaussianWeight a z t)*‖F z‖ := by
        rw [rieszGaussianWeight_integral ha hz]
        ring
      _ = ∫ t in Ioi (0:ℝ), rieszGaussianWeight a z t*‖F z‖ := (integral_mul_const _ _).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (rieszGaussianWeight_nonneg a z ht)]

/-- Fubini applied to the absolutely integrable Gaussian representation. -/
theorem riesz_integral_eq_gaussian_integral (F : 𝓢(ℂ,ℂ)) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) :
    (Real.Gamma a:ℂ)*(∫ z : ℂ, ((‖z‖^(-2*a):ℝ):ℂ)*F z) =
      ∫ t in Ioi (0:ℝ), ∫ z : ℂ, (rieszGaussianWeight a z t:ℂ)*F z := by
  calc
    _ = ∫ z : ℂ, ∫ t in Ioi (0:ℝ), (rieszGaussianWeight a z t:ℂ)*F z := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_complex_ne_zero] with z hz
      rw [integral_mul_const,integral_complex_ofReal,rieszGaussianWeight_integral ha hz]
      push_cast
      ring
    _ = _ := integral_integral_swap (integrable_riesz_gaussian_product F ha ha1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GaussianMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin change of variables for the Gaussian Riesz identity. -/

noncomputable section
open scoped SchwartzMap
open MeasureTheory Set
namespace CubicFirstMoment

lemma gaussian_mellin_identity (F : 𝓢(ℂ,ℂ)) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (Real.Gamma a:ℂ)*(∫ z : ℂ, ((‖z‖^(-2*a):ℝ):ℂ)*F z) =
      ∫ t in Ioi (0:ℝ), (t^(a-1):ℝ)*
        (∫ z : ℂ, F z*Complex.exp (-(t:ℂ)*‖z‖^2)) := by
  rw [riesz_integral_eq_gaussian_integral F ha ha1]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  unfold rieszGaussianWeight
  rw [Complex.ofReal_mul,Complex.ofReal_exp]
  push_cast
  rw [show -((‖z‖:ℂ)^2)*(t:ℂ) = -(t:ℂ)*(‖z‖:ℂ)^2 by ring]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RieszIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The trace Fourier Riesz identity at the two exponents needed for cubing. -/

noncomputable section
open scoped SchwartzMap
open MeasureTheory Set
namespace CubicFirstMoment

/-- The Riesz identity before dividing by Gamma(2/3). -/
theorem riesz_trace_identity (F : 𝓢(ℂ,ℂ)) :
    (Real.Gamma (2/3:ℝ):ℂ)*
      (∫ z : ℂ, ((‖z‖^(-(4/3:ℝ)):ℝ):ℂ)*traceFourier F z) =
      ((Real.pi*(4*Real.pi^2)^(-(1/3:ℝ))*Real.Gamma (1/3:ℝ):ℝ):ℂ)*
        (∫ z : ℂ, ((‖z‖^(-(2/3:ℝ)):ℝ):ℂ)*F z) := by
  let H (v : ℝ) := ∫ z : ℂ, F z*Complex.exp (-(v:ℂ)*‖z‖^2)
  let c : ℝ := 4*Real.pi^2
  have hc : 0 < c := by dsimp [c]; positivity
  have hstart := gaussian_mellin_identity (traceFourierSchwartz F)
    (a := 2/3) (by norm_num) (by norm_num)
  norm_num only at hstart
  simp only [traceFourierSchwartz_apply] at hstart
  have hfinish := gaussian_mellin_identity F (a := 1/3) (by norm_num) (by norm_num)
  norm_num only at hfinish
  have hheat (t : ℝ) (ht : 0 < t) :
      (∫ y : ℂ, traceFourier F y*Complex.exp (-(t:ℂ)*‖y‖^2)) =
        ((Real.pi/t:ℝ):ℂ)*H (c/t) := by
    rw [integral_traceFourier_gaussian F F.integrable ht]
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    dsimp only [H,c]
    congr 1
    congr 1
    rw [Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hpower (t : ℝ) (ht : 0 < t) :
      ((t^(-(1/3:ℝ)):ℝ):ℂ)*((Real.pi/t:ℝ):ℂ) =
        (Real.pi:ℂ)*((t^(-(4/3:ℝ)):ℝ):ℂ) := by
    have he : t^(-(1/3:ℝ))/t = t^(-(4/3:ℝ)) := by
      nth_rw 2 [← Real.rpow_one t]
      rw [← Real.rpow_sub ht]
      norm_num
    have hr : t^(-(1/3:ℝ))*(Real.pi/t) = Real.pi*t^(-(4/3:ℝ)) := by
      calc
        _ = Real.pi*(t^(-(1/3:ℝ))/t) := by ring
        _ = _ := by rw [he]
    exact_mod_cast hr
  rw [hstart]
  calc
    _ = (Real.pi:ℂ)*(∫ t in Ioi (0:ℝ), (t^(-(4/3:ℝ)):ℝ)*H (c/t)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [hheat t ht,← mul_assoc,hpower t ht,mul_assoc]
    _ = (Real.pi:ℂ)*((c^(-(1/3:ℝ)):ℝ):ℂ)*
        (∫ v in Ioi (0:ℝ), (v^(-(2/3:ℝ)):ℝ)*H v) := by
      have hi := inverse_mellin_change H (2/3) hc
      norm_num only at hi
      rw [hi,mul_assoc]
    _ = _ := by
      rw [← hfinish]
      dsimp only [c]
      push_cast
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeRiesz
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the actual cube-lattice integral with the model term. -/

noncomputable section
open scoped SchwartzMap ContDiff
open MeasureTheory
namespace CubicFirstMoment

lemma normProfileFourier_cubing_integral (W : ℝ → ℂ) :
    (∫ z : ℂ, normProfileFourier W (z^3)) =
      (1/3:ℂ)*(∫ z : ℂ, ((‖z‖^(-(4/3:ℝ)):ℝ):ℂ)*normProfileFourier W z) := by
  have h := radial_cubing_integral (fun r => radialDualProfile W (r^2))
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with z
    rw [normProfileFourier_radial,map_pow,Complex.normSq_eq_norm_sq]
    congr 1
    ring
  · congr 1
    apply integral_congr_ae
    filter_upwards with z
    rw [normProfileFourier_radial,Complex.normSq_eq_norm_sq]

/-- The exact Riesz constant for the trace pairing and covolume-one
Eisenstein measure. All Fourier and singular-integral steps are proved. -/
theorem cubeProfileIntegral_eq_model (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) :
    cubeProfileIntegral W = (cStar^2:ℝ) •
      ((2/Real.sqrt 3:ℝ) • (∫ z : ℂ, ((‖z‖^(-(2/3:ℝ)):ℝ):ℂ)*W (Complex.normSq z))) := by
  let F := normProfileSchwartz W hW hW' 1 (by norm_num)
  let ρ : ℝ := 2/Real.sqrt 3
  let C : ℝ := Real.pi*(4*Real.pi^2)^(-(1/3:ℝ))*Real.Gamma (1/3:ℝ)/Real.Gamma (2/3:ℝ)
  let J := ∫ z : ℂ, ((‖z‖^(-(2/3:ℝ)):ℝ):ℂ)*F z
  have hF (z : ℂ) : F z = W (Complex.normSq z) := by simp [F]
  have hFT (z : ℂ) : normProfileFourier W z = (ρ:ℂ)*traceFourier F z := by
    change (2/Real.sqrt 3:ℝ) • traceFourier (fun z => W (Complex.normSq z)) z = _
    rw [Complex.real_smul]
    congr 1
    apply congrArg (fun f : ℂ → ℂ => traceFourier f z)
    funext x
    exact (hF x).symm
  have htr : (∫ z : ℂ, ((‖z‖^(-(4/3:ℝ)):ℝ):ℂ)*traceFourier F z) = (C:ℂ)*J := by
    have h := riesz_trace_identity F
    have hg : (Real.Gamma (2/3:ℝ):ℂ) ≠ 0 := by
      exact_mod_cast (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 2/3)).ne'
    apply (mul_left_cancel₀ hg)
    dsimp only [C,J]
    rw [h]
    push_cast
    field_simp
  have hw : (∫ z : ℂ, ((‖z‖^(-(4/3:ℝ)):ℝ):ℂ)*normProfileFourier W z) =
      (ρ:ℂ)*(∫ z : ℂ, ((‖z‖^(-(4/3:ℝ)):ℝ):ℂ)*traceFourier F z) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    rw [hFT]
    ring
  have hr : (1/3:ℝ)*ρ*C = cStar^2 := by
    dsimp only [ρ,C]
    convert cubic_riesz_gaussian_constant using 1 <;> first | rfl | ring
  have hc : (1/3:ℂ)*(ρ:ℂ)*(C:ℂ) = ((cStar^2:ℝ):ℂ) := by
    have hh := congrArg Complex.ofReal hr
    push_cast at hh
    simpa only [Complex.ofReal_pow] using hh
  unfold cubeProfileIntegral
  rw [Complex.real_smul,normProfileFourier_cubing_integral,hw,htr]
  change (ρ:ℂ)*((1/3:ℂ)*((ρ:ℂ)*((C:ℂ)*J))) = _
  calc
    _ = ((cStar^2:ℝ):ℂ)*(ρ:ℂ)*J := by rw [← hc]; ring
    _ = _ := by
      simp only [Complex.real_smul]
      dsimp only [ρ,J]
      simp_rw [hF]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual area term in primary radial lattice summation. The
nonzero dual frequencies are bounded by the existing Schwartz estimate. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators SchwartzMap
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma integral_normSq_profile (W : ℝ → ℂ) :
    (∫ z : ℂ, W (Complex.normSq z)) = (Real.pi:ℂ)*(∫ x in Ioi (0:ℝ), W x) := by
  simp_rw [Complex.normSq_eq_norm_sq]
  rw [complex_radial_integral (fun r => W (r^2))]
  have hsub := integral_comp_rpow_Ioi W (show (2:ℝ) ≠ 0 by norm_num)
  have hh : (2:ℂ)*(∫ r in Ioi (0:ℝ), (r:ℂ)*W (r^2)) = ∫ x in Ioi (0:ℝ), W x := by
    rw [←integral_const_mul,←hsub]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2),show (2:ℝ)-1 = 1 by norm_num,Real.rpow_one,Real.rpow_two,
      Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]
    ring
  linear_combination (Real.pi:ℂ)*hh

theorem UniformLogWeights.radial_coset_error {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i q, q ≠ 0 → ∀ z : ℂ,
      ‖(∑' a : Eisenstein, W i (Complex.normSq (z+q*(a:ℂ))))-
        (2/(Real.sqrt 3*Complex.normSq q):ℝ) • (∫ w : ℂ, W i (Complex.normSq w))‖ ≤
        K*Complex.normSq q := by
  obtain ⟨D,hD,hbound⟩ := h.angularFourier_seminorm 0 4 0
  let R := ∑' a : Eisenstein, (norm a)^(-(2:ℝ))
  have hR : 0 ≤ R := tsum_nonneg (fun a => Real.rpow_nonneg (norm_nonneg a) _)
  let C := D*R+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨18*C/Real.sqrt 3,by positivity,?_⟩
  intro i q hq z
  let F := angularAnnulusSchwartz 0 (W i) (h.compact i) (h.positive i) (h.smooth i)
  have hF (w : ℂ) : F w = W i (Complex.normSq w) := by simp [F,angularAnnulusSchwartz,angularAnnulus,angularPlanePhase]
  have hd : ∀ w : ℂ, ‖w‖^4*‖traceFourier F w‖ ≤ D := by
    intro w
    have hh := SchwartzMap.le_seminorm ℝ 4 0 (traceFourierSchwartz F) w
    simp only [norm_iteratedFDeriv_zero,traceFourierSchwartz_apply] at hh
    exact hh.trans (hbound i)
  have hN : 0 < Complex.normSq q := Complex.normSq_pos.mpr hq
  have hw : q*traceLambda ≠ 0 := mul_ne_zero hq traceLambda_ne_zero
  let c : Eisenstein → ℂ := fun a =>
    (Real.fourierChar (tracePair z ((a:ℂ)/(q*traceLambda))) : ℂ)
  have hc : ∀ a, ‖c a‖ ≤ 1 := by
    intro a
    exact (Circle.norm_coe _).le
  have hs : Summable (fun a : Eisenstein => c a*traceFourier F ((a:ℂ)/(q*traceLambda))) := by
    apply (traceFourier_summable_eisenstein F _ hw).norm.of_norm_bounded
    intro a
    rw [norm_mul]
    exact mul_le_of_le_one_left (_root_.norm_nonneg _) (hc a)
  have hzero : c 0*traceFourier F (((0:Eisenstein):ℂ)/(q*traceLambda)) = ∫ w : ℂ, F w := by
    simp [c,traceFourier_zero,tracePair]
  simp_rw [←hF]
  rw [poisson_eisenstein_coset F q hq z]
  change ‖(2/(Real.sqrt 3*Complex.normSq q):ℝ) •
    (∑' a : Eisenstein, c a*traceFourier F ((a:ℂ)/(q*traceLambda)))-
    (2/(Real.sqrt 3*Complex.normSq q):ℝ) • (∫ w : ℂ, F w)‖ ≤ _
  rw [hs.tsum_eq_add_tsum_ite 0,hzero,smul_add,add_sub_cancel_left,norm_smul,
    Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (schwartz_weighted_dual_bound F hD.le hd _ hw c hc)
    (by positivity)).trans_eq
  rw [Complex.normSq_mul,traceLambda_normSq]
  dsimp [C,R]
  field_simp
  ring

theorem UniformLogWeights.primaryRadialLattice_error {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i Y, 0 < Y →
      ‖primaryAngularLattice 0 (W i) Y-primaryRadialMain (W i) Y‖ ≤ K/Y := by
  obtain ⟨C,hC,hbound⟩ := h.radial_coset_error
  refine ⟨9*C,by positivity,?_⟩
  intro i Y hY
  let s : ℝ := 1/Real.sqrt Y
  have hs : 0 < s := by dsimp [s]; positivity
  have hq : (s:ℂ)*3 ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne') (by norm_num)
  have hn : Complex.normSq ((s:ℂ)*3) = 9/Y := by
    rw [Complex.normSq_mul,Complex.normSq_ofReal]
    norm_num
    dsimp [s]
    rw [one_div,←pow_two,inv_pow,Real.sq_sqrt hY.le]
    ring
  have he : primaryAngularLattice 0 (W i) Y =
      ∑' u : PrimaryArgument, W i (Complex.normSq ((s:ℂ)*(u:ℂ))) := by
    apply tsum_congr
    intro u
    simpa only [angularAnnulus,angularPlanePhase,zpow_zero,one_mul] using
      (angularAnnulus_scaled 0 (W i) hY u).symm
  rw [he,primary_scaled_coset (fun z : ℂ => W i (Complex.normSq z)) (s:ℂ)]
  have hb := hbound i _ hq (s:ℂ)
  rw [hn,integral_normSq_profile] at hb
  have hm : (2/(Real.sqrt 3*(9/Y)):ℝ) • ((Real.pi:ℂ)*(∫ x in Ioi (0:ℝ), W i x)) =
      primaryRadialMain (W i) Y := by
    rw [Complex.real_smul,primaryRadialMain]
    push_cast
    field_simp
  rw [hm] at hb
  exact hb.trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeRieszMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put the proved cube Riesz integral in the same radial Mellin
normalization as the squarefree lattice density. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma integral_radial_third_weight (W : ℝ → ℂ) :
    (∫ x in Ioi (0:ℝ), ((x^(-1/3:ℝ):ℝ):ℂ)*W x) = mellin W (2/3) := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [Complex.ofReal_cpow hx.le]
  norm_num

lemma integral_plane_third_weight (W : ℝ → ℂ) :
    (∫ z : ℂ, ((‖z‖^(-2/3:ℝ):ℝ):ℂ)*W (Complex.normSq z)) =
      (Real.pi:ℂ)*mellin W (2/3) := by
  calc
    _ = ∫ z : ℂ, (((Complex.normSq z)^(-1/3:ℝ):ℝ):ℂ)*W (Complex.normSq z) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [Complex.normSq_eq_norm_sq,←Real.rpow_natCast ‖z‖ 2,
        ←Real.rpow_mul (_root_.norm_nonneg z)]
      norm_num
    _ = (Real.pi:ℂ)*(∫ x in Ioi (0:ℝ), ((x^(-1/3:ℝ):ℝ):ℂ)*W x) :=
      integral_normSq_profile (fun x => ((x^(-1/3:ℝ):ℝ):ℂ)*W x)
    _ = _ := by rw [integral_radial_third_weight]

theorem cubeProfileIntegral_eq_mellin (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) :
    cubeProfileIntegral W = ((cStar^2*(2*Real.pi/Real.sqrt 3):ℝ):ℂ)*mellin W (2/3) := by
  rw [cubeProfileIntegral_eq_model W hW hW']
  simp_rw [show -(2/3:ℝ) = -2/3 by ring]
  rw [integral_plane_third_weight]
  simp only [Complex.real_smul]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialCentered
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform centered radial lattice sums, including the short empty range.
The coprimality correction is a literal finite Möbius expansion. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma UniformLogWeights.radial_integral_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ M : ℝ, 0 < M ∧ ∀ i, ‖∫ x in Ioi (0:ℝ), W i x‖ ≤ M := by
  obtain ⟨M,hM,hb⟩ := h.mellin_decay 1 0
  refine ⟨M,hM,?_⟩
  intro i
  have hh := hb i 1 (by norm_num) 0
  simpa [mellin] using hh

theorem UniformLogWeights.primaryRadialLattice_centered {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i Y, 0 < Y →
      ‖primaryAngularLattice 0 (W i) Y-primaryRadialMain (W i) Y‖ ≤ K := by
  obtain ⟨C,hC,hbound⟩ := h.primaryRadialLattice_error
  obtain ⟨M,hM,hMbound⟩ := h.radial_integral_bound
  let S := Real.exp h.radius
  have hS : 1 ≤ S := Real.one_le_exp h.radius_nonneg
  have hSpos : 0 < S := Real.exp_pos _
  let A := 2*Real.pi/(9*Real.sqrt 3)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨C*S+A*M,by positivity,?_⟩
  intro i Y hY
  by_cases he : 1 ≤ S*Y
  · apply (hbound i Y hY).trans
    have hh : C/Y ≤ C*S := (div_le_iff₀ hY).mpr (by nlinarith)
    exact hh.trans (le_add_of_nonneg_right (mul_nonneg hA hM.le))
  · have hz : primaryAngularLattice 0 (W i) Y = 0 := by
      have ht (u : PrimaryArgument) : theta 0 u*W i (norm u/Y) = 0 := by
        have hn := one_le_norm (primary_ne_zero u.property)
        have hw : W i (norm u/Y) = 0 := h.upper_support i _
          ((lt_div_iff₀ hY).mpr ((lt_of_not_ge he).trans_le hn))
        rw [hw,mul_zero]
      simp only [primaryAngularLattice,ht,tsum_zero]
    have hY1 : Y ≤ 1 := by nlinarith
    have hm : ‖primaryRadialMain (W i) Y‖ ≤ A*M := by
      rw [primaryRadialMain,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      change (2*Real.pi*Y/(9*Real.sqrt 3))*_ ≤ A*M
      calc
        _ = (A*Y)*‖∫ x in Ioi (0:ℝ), W i x‖ := by dsimp [A]; ring
        _ ≤ A*M := by
          apply mul_le_mul
          · exact mul_le_of_le_one_right hA hY1
          · exact hMbound i
          · positivity
          · exact hA
    rw [hz,zero_sub,norm_neg]
    exact hm.trans (le_add_of_nonneg_left (by positivity))

theorem UniformLogWeights.primaryCoprimeRadialLattice_centered
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ Y, 0 < Y →
      ‖primaryCoprimeAngularLattice r 0 (W i) Y-primaryCoprimeRadialMain r (W i) Y‖ ≤
        K*norm r^ε := by
  obtain ⟨C,hC,hbound⟩ := h.primaryRadialLattice_centered
  obtain ⟨D,hD,hdiv⟩ := primeDivisorWeight_small_power ε hε
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro i r hr hsr Y hY
  rw [primaryCoprimeAngularLattice_expansion hr hsr 0 (W i) (h.compact i) (h.smooth i) hY,
    primaryCoprimeRadialMain,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ s ∈ (primaryPrimeFactors r).powerset,C := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro s hs
      have hd : primary (∏ p ∈ s,p) := primary_finset_prod _ _
        (fun p hp => (primaryPrimeFactor_spec hr (Finset.mem_powerset.mp hs hp)).1.1)
      have hθ : theta 0 (∏ p ∈ s,p) = 1 := by simp [theta]
      rw [hθ,mul_one,←mul_sub,norm_mul]
      exact (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _)).trans
        (hbound i _ (div_pos hY (norm_pos_of_ne_zero (primary_ne_zero hd))))
    _ = C*(2:ℝ)^(primaryPrimeFactors r).card := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring
    _ ≤ C*(D*norm r^ε) := mul_le_mul_of_nonneg_left (hdiv r hr hsr) hC.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTotient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite coprimality density at a squarefree primary level.
Only residue-ring cardinalities and the ordinary Chinese remainder theorem
enter this calculation. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticTotient_mul {a b : Eisenstein} (hab : IsCoprime a b) :
    metaplecticTotient (a*b) = metaplecticTotient a*metaplecticTotient b := by
  let e : Residues (a*b) ≃+* Residues a × Residues b :=
    (Ideal.quotEquivOfEq (show modulus (a*b) = modulus a*modulus b by
      exact (Ideal.span_singleton_mul_span_singleton a b).symm)).trans
      (Ideal.quotientMulEquivQuotientProd _ _
        ((Ideal.isCoprime_span_singleton_iff a b).mpr hab))
  have hc := Nat.card_congr ((Units.mapEquiv e.toMulEquiv).trans MulEquiv.prodUnits).toEquiv
  simpa only [metaplecticTotient,Nat.card_prod,Nat.cast_mul] using congrArg (fun n : ℕ => (n:ℝ)) hc

lemma metaplecticTotient_prime {p : Eisenstein} (hp : primaryPrime p) :
    metaplecticTotient p = norm p-1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  have hn : 1 ≤ normNat p := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (normNat_ne_zero hp.2.ne_zero))
  rw [metaplecticTotient,Nat.card_units,residues_card hp.2.ne_zero,Nat.cast_sub hn,normNat_cast]
  norm_num

lemma metaplecticTotient_prod (s : Finset Eisenstein)
    (hp : ∀ p ∈ s, primaryPrime p) :
    metaplecticTotient (∏ p ∈ s,p) = ∏ p ∈ s,(norm p-1) := by
  induction s using Finset.induction_on with
  | empty =>
      change (Nat.card (Residues (1:Eisenstein))ˣ:ℝ) = 1
      have hc : Nat.card (Residues (1:Eisenstein)) = 1 := by
        rw [residues_card one_ne_zero,normNat_one]
      have hsub : Subsingleton (Residues (1:Eisenstein)) :=
        (Nat.card_eq_one_iff_unique.mp hc).1
      have hunit : ∀ u : (Residues (1:Eisenstein))ˣ, u = 1 := by
        intro u
        apply Units.ext
        exact hsub.elim _ _
      have hu : Nat.card (Residues (1:Eisenstein))ˣ = 1 :=
        Nat.card_eq_one_iff_exists.mpr ⟨1,hunit⟩
      exact_mod_cast hu
  | @insert p s hps ih =>
      have hp' := hp p (Finset.mem_insert_self _ _)
      have hs : ∀ q ∈ s, primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
      have hc : IsCoprime p (∏ q ∈ s,q) := by
        apply IsCoprime.prod_right
        intro q hq
        exact primaryPrimes_isCoprime hp' (hs q hq) (fun heq => hps (heq ▸ hq))
      rw [Finset.prod_insert hps,metaplecticTotient_mul hc,metaplecticTotient_prime hp',
        ih hs,Finset.prod_insert hps]

lemma metaplecticTotient_density {r : Eisenstein} (hr : primary r) (hsr : Squarefree r) :
    metaplecticTotient r/norm r =
      ∏ p ∈ primaryPrimeFactors r,(1-(norm p)⁻¹) := by
  have hp : ∀ p ∈ primaryPrimeFactors r, primaryPrime p :=
    fun p hp => (primaryPrimeFactor_spec hr hp).1
  have hn : (∏ p ∈ primaryPrimeFactors r,norm p) = norm r := by
    rw [←norm_finset_prod,primaryPrimeFactors_prod hr hsr]
  have hφ := metaplecticTotient_prod (primaryPrimeFactors r) hp
  rw [primaryPrimeFactors_prod hr hsr] at hφ
  rw [hφ]
  rw [←hn,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp'
  have hnp := norm_pos_of_ne_zero (primary_ne_zero (hp p hp').1)
  field_simp

lemma primary_moebius_density {r : Eisenstein} (hr : primary r) (hsr : Squarefree r) :
    (∑ s ∈ (primaryPrimeFactors r).powerset,
      (idealMoebius (∏ p ∈ s,p):ℝ)/norm (∏ p ∈ s,p)) = metaplecticTotient r/norm r := by
  rw [metaplecticTotient_density hr hsr,Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro s hs
  have hp : ∀ p ∈ s, primaryPrime p := fun p hp =>
    (primaryPrimeFactor_spec hr (Finset.mem_powerset.mp hs hp)).1
  rw [idealMoebius_prod_primaryPrimes s hp]
  simp only [Finset.prod_const_one,mul_one]
  rw [Finset.prod_inv_distrib]
  have hn : (∏ p ∈ s,norm p) = norm (∏ p ∈ s,p) := (norm_finset_prod _ _).symm
  rw [hn]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialDensity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the radial lattice density with the literal
metaplectic residue constant. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryCoprimeRadialMain_eq {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) (Y : ℝ) :
    primaryCoprimeRadialMain r W Y =
      (((2*Real.pi*Y/(9*Real.sqrt 3))*(metaplecticTotient r/norm r):ℝ):ℂ)*
        (∫ x in Ioi (0:ℝ), W x) := by
  have hsum : (∑ s ∈ (primaryPrimeFactors r).powerset,
      ((idealMoebius (∏ p ∈ s,p):ℝ)/norm (∏ p ∈ s,p):ℝ)) =
      metaplecticTotient r/norm r := primary_moebius_density hr hsr
  unfold primaryCoprimeRadialMain primaryRadialMain
  calc
    _ = (∑ s ∈ (primaryPrimeFactors r).powerset,
        (((idealMoebius (∏ p ∈ s,p):ℝ)/norm (∏ p ∈ s,p):ℝ):ℂ))*
          (((2*Real.pi*Y/(9*Real.sqrt 3)):ℝ):ℂ)*(∫ x in Ioi (0:ℝ), W x) := by
      rw [Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      push_cast
      ring
    _ = _ := by rw [←Complex.ofReal_sum,hsum,Complex.ofReal_mul]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticSquarefreeRadial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squarefree radial model after actual square-divisor inversion.
Its finite main term remains explicit for comparison with the inverse
completion residue. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefreeCoprimeRadialMain_eq {r : Eisenstein} (hr : primary r)
    (hsr : Squarefree r) (W : ℝ → ℂ) (Y B : ℝ) :
    squarefreeCoprimeRadialMain r W Y B =
      ((((2*Real.pi*Y/(9*Real.sqrt 3))*(metaplecticTotient r/norm r):ℝ):ℂ)*
        (∫ x in Set.Ioi (0:ℝ), W x))*
          metaplecticRadialEulerPartial r (Real.sqrt (B*Y)) := by
  have he : squarefreeDivisorTruncation (Real.sqrt (B*Y)) =
      (primaryElementBall (Real.sqrt (B*Y))).filter Squarefree := by
    ext c
    simp only [mem_squarefreeDivisorTruncation,Finset.mem_filter,mem_primaryElementBall]
    tauto
  unfold squarefreeCoprimeRadialMain metaplecticRadialEulerPartial
  rw [he,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hsf : Squarefree c
  · simp only [hsf,ite_true, if_true]
    have hcop : IsCoprime r (c^2) ↔ IsCoprime r c := by
      rw [pow_two,IsCoprime.mul_right_iff,and_self]
    by_cases hrc : IsCoprime r c
    · simp only [hcop,hrc,ite_true, if_true,primaryCoprimeRadialMain_eq hr hsr]
      rw [eisenstein_norm_pow_lattice,Real.rpow_neg (norm_nonneg c),Real.rpow_ofNat]
      push_cast
      ring
    · simp only [hcop,hrc,ite_false, if_false,mul_zero]
  · simp [hsf,idealMoebius]

theorem UniformLogWeights.squarefreeCoprimeRadialLattice_centered
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ Y, 0 < Y →
      ‖squarefreeCoprimeAngularLattice r 0 (W i) Y-
        squarefreeCoprimeRadialMain r (W i) Y (Real.exp h.radius)‖ ≤
        K*norm r^ε*Real.sqrt Y := by
  obtain ⟨C,hC,hbound⟩ := h.primaryCoprimeRadialLattice_centered hε
  let S := Real.exp h.radius
  have hS : 0 < S := Real.exp_pos _
  refine ⟨18*Real.sqrt S*C,by positivity,?_⟩
  intro i r hr hsr Y hY
  have hNr : 0 ≤ norm r^ε := Real.rpow_nonneg (norm_nonneg r) _
  let B := squarefreeDivisorTruncation (Real.sqrt (S*Y))
  have hcard : (B.card:ℝ) ≤ 18*Real.sqrt (S*Y) := by
    have hsub : B ⊆ nonzeroNormBall (Real.sqrt (S*Y)) := by
      intro c hc
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (nonzeroNormBall_card_le (Real.sqrt_nonneg _))
  rw [squarefreeCoprimeAngularLattice_expansion r 0 (W i) (h.compact i) (h.smooth i)
    hY (h.upper_support i),squarefreeCoprimeRadialMain,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c ∈ B,C*norm r^ε := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro c hc
      have hprim : primary (c^2) := by
        simpa only [pow_two] using primary_mul (mem_squarefreeDivisorTruncation.mp hc).1
          (mem_squarefreeDivisorTruncation.mp hc).1
      by_cases hcop : IsCoprime r (c^2)
      · simp only [hcop,ite_true, if_true,show theta 0 (c^2) = 1 by simp [theta],one_mul]
        rw [←mul_sub,norm_mul]
        exact (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _)).trans
          (hbound i r hr hsr _ (div_pos hY (norm_pos_of_ne_zero (primary_ne_zero hprim))))
      · simp only [hcop,ite_false, if_false,mul_zero,sub_self,norm_zero]
        exact mul_nonneg hC.le hNr
    _ = (B.card:ℝ)*(C*norm r^ε) := by simp
    _ ≤ (18*Real.sqrt (S*Y))*(C*norm r^ε) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hC.le hNr)
    _ = _ := by rw [Real.sqrt_mul hS.le]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeModelMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal squarefree mass occurring in the corrected model,
written in the radial lattice normalization. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefreeModelMass_eq_radial {A : ℝ} (hA : 0 < A) (W : ℝ → ℂ) :
    squarefreeModelMass W A = ((A^(-1/3:ℝ):ℝ):ℂ)*
      squarefreeCoprimeAngularLattice 1 0 (fun x => ((x^(-1/3:ℝ):ℝ):ℂ)*W x) A := by
  rw [squarefreeModelMass,squarefreeCoprimeAngularLattice,←tsum_mul_left]
  apply tsum_congr
  intro a
  by_cases ha : primary a
  · have hp : norm a^(-1/3:ℝ) = A^(-1/3:ℝ)*(norm a/A)^(-1/3:ℝ) := by
      rw [←Real.mul_rpow hA.le (div_nonneg (norm_nonneg a) hA.le),
        mul_div_cancel₀ _ hA.ne']
    simp only [ha,isCoprime_one_left,and_self,ite_true, if_true,theta_zero,hp]
    push_cast
    ring
  · simp only [ha,false_and,ite_false, if_false,mul_zero]

lemma squarefreeRadialMain_one_scaled (W : ℝ → ℂ) {A : ℝ} (hA : 0 < A) (B : ℝ) :
    ((A^(-1/3:ℝ):ℝ):ℂ)*
      squarefreeCoprimeRadialMain 1 (fun x => ((x^(-1/3:ℝ):ℝ):ℂ)*W x) A B =
    ((A^(2/3:ℝ)*(2*Real.pi/(9*Real.sqrt 3)):ℝ):ℂ)*mellin W (2/3)*
      metaplecticRadialEulerPartial 1 (Real.sqrt (B*A)) := by
  have hφ : metaplecticTotient 1 = 1 := by
    simpa using metaplecticTotient_prod (∅ : Finset Eisenstein) (by simp)
  have hp : A^(-1/3:ℝ)*A = A^(2/3:ℝ) := by
    calc
      _ = A^(-1/3:ℝ)*A^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hA]; norm_num
  rw [squarefreeCoprimeRadialMain_eq primary_one squarefree_one,
    integral_radial_third_weight,hφ,norm_one_eq]
  simp only [div_one,mul_one]
  push_cast
  calc
    _ = ((A^(-1/3:ℝ)*A:ℝ):ℂ)*(2*Real.pi/(9*Real.sqrt 3))*mellin W (2/3)*
        metaplecticRadialEulerPartial 1 (Real.sqrt (B*A)) := by push_cast; ring
    _ = _ := by rw [hp]

theorem UniformLogWeights.squarefreeModelMass_finite_error
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i A, 0 < A →
      ‖squarefreeModelMass (W i) A-
        ((A^(2/3:ℝ)*(2*Real.pi/(9*Real.sqrt 3)):ℝ):ℂ)*mellin (W i) (2/3)*
          metaplecticRadialEulerPartial 1
            (Real.sqrt (Real.exp (h.realPower (-1/3)).radius*A))‖ ≤ K*A^(1/6:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := (h.realPower (-1/3)).squarefreeCoprimeRadialLattice_centered
    (show (0:ℝ) < 1 by norm_num)
  refine ⟨K,hK,?_⟩
  intro i A hA
  rw [squarefreeModelMass_eq_radial hA,
    ←squarefreeRadialMain_one_scaled (W i) hA,←mul_sub,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hA _)]
  calc
    _ ≤ A^(-1/3:ℝ)*(K*norm (1:Eisenstein)^(1:ℝ)*Real.sqrt A) :=
      mul_le_mul_of_nonneg_left (hbound i 1 primary_one squarefree_one A hA)
        (Real.rpow_nonneg hA.le _)
    _ = K*A^(1/6:ℝ) := by
      rw [norm_one_eq,Real.one_rpow,mul_one,Real.sqrt_eq_rpow]
      calc
        _ = K*(A^(-1/3:ℝ)*A^(1/2:ℝ)) := by ring
        _ = _ := by rw [←Real.rpow_add hA]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeCoprimeRemoval
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the true mutual-coprimality restriction costs the density
of multiples of the actual prime factors, not an assumed error term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefreeCoprimeRadial_eq_sum (r : Eisenstein) (W : ℝ → ℂ)
    {A R : ℝ} (hA : 0 < A) (hcut : ∀ x, R < x → W x = 0) :
    squarefreeCoprimeAngularLattice r 0 W A =
      ∑ a ∈ primaryElementBall (R*A), if IsCoprime r a then
        (idealMoebius a:ℂ)^2*W (norm a/A) else 0 := by
  unfold squarefreeCoprimeAngularLattice
  simp only [theta_zero,mul_one]
  calc
    _ = ∑ a ∈ primaryElementBall (R*A), if primary a ∧ IsCoprime r a then
        (idealMoebius a:ℂ)^2*W (norm a/A) else 0 := by
      apply tsum_eq_sum
      intro a ha
      by_cases hp : primary a
      · have hn : R < norm a/A := by
          apply (lt_div_iff₀ hA).mpr
          exact lt_of_not_ge (fun hn => ha (mem_primaryElementBall.mpr ⟨hp,hn⟩))
        simp only [hcut _ hn,mul_zero,ite_self]
      · simp only [hp,false_and,ite_false, if_false]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [(mem_primaryElementBall.mp ha).1,true_and]

lemma squarefreeCoprimeRadial_difference_bound (W : ℝ → ℂ)
    {A R M D : ℝ} (hA : 0 < A) (hR : 0 ≤ R) (hM : 0 ≤ M) (hD : 0 < D)
    (hcut : ∀ x, R < x → W x = 0) (hW : ∀ x, ‖W x‖ ≤ M)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (hrough : ∀ p ∈ primaryPrimeFactors r, D ≤ norm p) :
    ‖squarefreeCoprimeAngularLattice r 0 W A-
      squarefreeCoprimeAngularLattice 1 0 W A‖ ≤
      M*(primaryPrimeFactors r).card*(18*(R*A)/D) := by
  let S := primaryElementBall (R*A)
  rw [squarefreeCoprimeRadial_eq_sum r W hA hcut,
    squarefreeCoprimeRadial_eq_sum 1 W hA hcut]
  simp only [isCoprime_one_left,ite_true, if_true]
  rw [←Finset.sum_sub_distrib]
  have hp (a : Eisenstein) :
      ‖(if IsCoprime r a then (idealMoebius a:ℂ)^2*W (norm a/A) else 0)-
        (idealMoebius a:ℂ)^2*W (norm a/A)‖ ≤ if ¬IsCoprime r a then M else 0 := by
    by_cases ha : IsCoprime r a
    · simp only [ha,ite_true, if_true,not_true_eq_false,ite_false, if_false,sub_self,norm_zero,le_refl]
    · simp only [ha,ite_false, if_false,not_false_eq_true,ite_true, if_true,zero_sub,norm_neg,norm_mul,norm_pow]
      exact (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_idealMoebius_le_one a) 2)
        (_root_.norm_nonneg _)).trans (by simpa using hW (norm a/A))
  have hcard := noncoprime_row_card_le S (mul_nonneg hR hA.le) hD
    (fun a ha => ⟨primary_ne_zero (mem_primaryElementBall.mp ha).1,
      (mem_primaryElementBall.mp ha).2⟩) hr hsr hrough
  calc
    _ ≤ ∑ a ∈ S, if ¬IsCoprime r a then M else 0 :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => hp a))
    _ = ((S.filter (fun a => ¬IsCoprime r a)).card:ℝ)*M := by rw [←Finset.sum_filter]; simp
    _ ≤ ((primaryPrimeFactors r).card*(18*(R*A)/D))*M := mul_le_mul_of_nonneg_right hcard hM
    _ = _ := by ring

theorem UniformLogWeights.squarefreeCoprimeRadial_removal
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i (r : Eisenstein) (A D : ℝ),
      primary r → Squarefree r → 0 < A → 0 < D →
      (∀ p ∈ primaryPrimeFactors r, D ≤ norm p) →
      ‖squarefreeCoprimeAngularLattice r 0 (W i) A-
        squarefreeCoprimeAngularLattice 1 0 (W i) A‖ ≤
        K*A*(primaryPrimeFactors r).card/D := by
  obtain ⟨M,hM,hbound⟩ := h.norm_bound
  let R := Real.exp h.radius
  refine ⟨18*M*R,by dsimp [R]; positivity,?_⟩
  intro i r A D hr hsr hA hD hrough
  apply (squarefreeCoprimeRadial_difference_bound (W i) hA
    (Real.exp_pos _).le hM hD (h.upper_support i) (hbound i) hr hsr hrough).trans_eq
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeSquarefreeMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal mixed-term model with μ²(ra), and its quantitative
comparison with the unrestricted squarefree mass. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coprimeSquarefreeModelMass_eq_radial {r : Eisenstein} (hr : Squarefree r)
    {A : ℝ} (hA : 0 < A) (W : ℝ → ℂ) :
    coprimeSquarefreeModelMass r W A = ((A^(-1/3:ℝ):ℝ):ℂ)*
      squarefreeCoprimeAngularLattice r 0 (fun x => ((x^(-1/3:ℝ):ℝ):ℂ)*W x) A := by
  rw [coprimeSquarefreeModelMass,squarefreeCoprimeAngularLattice,←tsum_mul_left]
  apply tsum_congr
  intro a
  rw [idealMoebius_sq_mul_of_squarefree hr]
  by_cases ha : primary a
  · by_cases hc : IsCoprime r a
    · have hp : norm a^(-1/3:ℝ) = A^(-1/3:ℝ)*(norm a/A)^(-1/3:ℝ) := by
        rw [←Real.mul_rpow hA.le (div_nonneg (norm_nonneg a) hA.le),
          mul_div_cancel₀ _ hA.ne']
      simp only [ha,hc,true_and,ite_true, if_true,theta_zero,hp]
      push_cast
      ring
    · simp only [ha,hc,true_and,ite_true, if_true,ite_false, if_false,zero_mul,mul_zero]
  · simp only [ha,false_and,ite_false, if_false,mul_zero]

theorem UniformLogWeights.coprimeSquarefreeModelMass_error
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i (r : Eisenstein) (A D : ℝ),
      primary r → Squarefree r → 0 < A → 0 < D →
      (∀ p ∈ primaryPrimeFactors r, D ≤ norm p) →
      ‖coprimeSquarefreeModelMass r (W i) A-squarefreeModelMass (W i) A‖ ≤
        K*A^(2/3:ℝ)*(primaryPrimeFactors r).card/D := by
  obtain ⟨K,hK,hbound⟩ := (h.realPower (-1/3)).squarefreeCoprimeRadial_removal
  refine ⟨K,hK,?_⟩
  intro i r A D hr hsr hA hD hrough
  rw [coprimeSquarefreeModelMass_eq_radial hsr hA,squarefreeModelMass_eq_radial hA,
    ←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hA _)]
  apply (mul_le_mul_of_nonneg_left (hbound i r A D hr hsr hA hD hrough)
    (Real.rpow_nonneg hA.le _)).trans_eq
  have hp : A^(-1/3:ℝ)*A = A^(2/3:ℝ) := by
    calc
      _ = A^(-1/3:ℝ)*A^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hA]; norm_num
  calc
    _ = K*(A^(-1/3:ℝ)*A)*(primaryPrimeFactors r).card/D := by ring
    _ = _ := by rw [hp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAbsoluteModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma norm_dispersionModel_le_absolute (S : Finset Eisenstein) (β : Eisenstein → ℂ) (u : ℝ) :
    ‖dispersionModel S β u‖ ≤ dispersionAbsoluteModel S β := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  simp only [norm_mul,norm_normTwist,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg b) _),le_refl]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MixedModelCoprime
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal Type-I product model becomes the factored squarefree
model after a proved rough-prime coprimality error. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma mixedMassModel_sub_factor (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    mixedMassModel S β u W A-(cStar:ℂ)*dispersionModel S β u*squarefreeModelMass W A =
      (cStar:ℂ)*∑ b ∈ S, β b*normTwist u b*((norm b^(-1/6:ℝ):ℝ):ℂ)*
        (coprimeSquarefreeModelMass b W A-squarefreeModelMass W A) := by
  unfold mixedMassModel dispersionModel
  rw [mul_assoc,Finset.sum_mul,←mul_sub,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedMixedModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coprimality removal in the literal stopped mixed model. Roughness is
required only at nonzero coefficients; the original support is retained. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem UniformLogWeights.active_mixedMassModel_error
    {α : Type*} {W : α → ℝ → ℂ} (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (u A R Q : ℝ), 0 < A → 0 < R → 0 ≤ Q →
      (∀ b ∈ S, primary b ∧ Squarefree b) →
      (∀ b ∈ S, β b ≠ 0 → ((primaryPrimeFactors b).card:ℝ) ≤ Q) →
      (∀ b ∈ S, β b ≠ 0 → ∀ p ∈ primaryPrimeFactors b, R ≤ norm p) →
      ‖mixedMassModel S β u (W i) A-
        (cStar:ℂ)*dispersionModel S β u*squarefreeModelMass (W i) A‖ ≤
        K*Q*A^(2/3:ℝ)/R*dispersionAbsoluteModel S β := by
  obtain ⟨K,hK,hbound⟩ := h.coprimeSquarefreeModelMass_error
  refine ⟨cStar*K,mul_nonneg cStar_pos.le hK,?_⟩
  intro i S β u A R Q hA hR hQ hS hcard hrough
  rw [mixedMassModel_sub_factor,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos cStar_pos]
  have ht (b : Eisenstein) (hb : b ∈ S) :
      ‖β b*normTwist u b*((norm b^(-1/6:ℝ):ℝ):ℂ)*
        (coprimeSquarefreeModelMass b (W i) A-squarefreeModelMass (W i) A)‖ ≤
        (‖β b‖*norm b^(-1/6:ℝ))*(K*Q*A^(2/3:ℝ)/R) := by
    by_cases hz : β b = 0
    · simp [hz]
    rw [norm_mul,norm_mul,norm_mul,norm_normTwist,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg b) _)]
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg (_root_.norm_nonneg _) (Real.rpow_nonneg (norm_nonneg b) _))
    apply (hbound i b A R (hS b hb).1 (hS b hb).2 hA hR (hrough b hb hz)).trans
    calc
      _ ≤ K*A^(2/3:ℝ)*Q/R := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcard b hb hz) (by positivity)) hR.le
      _ = _ := by ring
  calc
    _ ≤ cStar*(∑ b ∈ S, (‖β b‖*norm b^(-1/6:ℝ))*(K*Q*A^(2/3:ℝ)/R)) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum ht)) cStar_pos.le
    _ = _ := by rw [←Finset.sum_mul]; unfold dispersionAbsoluteModel; ring

lemma bounded_annular_absolute_model (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M)
    (hS : ∀ a ∈ S, primary a ∧ b/2 ≤ norm a ∧ norm a ≤ b)
    (hβ : ∀ a ∈ S, ‖β a‖ ≤ M) :
    dispersionAbsoluteModel S β ≤ (18*(2:ℝ)^(1/6:ℝ)*M)*b^(5/6:ℝ) := by
  have ht (a : Eisenstein) (ha : a ∈ S) :
      ‖β a‖*norm a^(-1/6:ℝ) ≤ M*(b/2)^(-1/6:ℝ) :=
    mul_le_mul (hβ a ha)
      (Real.rpow_le_rpow_of_nonpos (by positivity) (hS a ha).2.1 (by norm_num))
      (Real.rpow_nonneg (norm_nonneg a) _) hM
  have hp : b*(b/2)^(-1/6:ℝ) = (2:ℝ)^(1/6:ℝ)*b^(5/6:ℝ) := by
    rw [Real.div_rpow hb.le (by norm_num),div_eq_mul_inv,
      ←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    norm_num only [neg_div,neg_neg]
    calc
      _ = (2:ℝ)^(1/6:ℝ)*(b^(1:ℝ)*b^(-1/6:ℝ)) := by rw [Real.rpow_one]; ring_nf
      _ = _ := by rw [←Real.rpow_add hb]; norm_num
  calc
    _ ≤ ∑ _a ∈ S, M*(b/2)^(-1/6:ℝ) := Finset.sum_le_sum ht
    _ = (S.card:ℝ)*(M*(b/2)^(-1/6:ℝ)) := by simp
    _ ≤ (18*b)*(M*(b/2)^(-1/6:ℝ)) := mul_le_mul_of_nonneg_right
      (primary_support_card_le S hb.le (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩))
      (by positivity)
    _ = (18*M)*(b*(b/2)^(-1/6:ℝ)) := by ring
    _ = _ := by rw [hp]; ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_mixed_model_log_saving {ξ κ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hκ : 0 < κ) (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦpos : tsupport Φ ⊆ Set.Ioi 0) (hΦ' : ContDiff ℝ ∞ Φ) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b A u : ℝ), 0 < δ → δ ≤ 1 → X^κ ≤ b → b ≤ X → 0 < A →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (e : Eisenstein) (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      (Real.log X)^(k+1) ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      ‖((cStar:ℂ)*star (dispersionModel S β u))*(mixedMassModel S β u Φ A-
        (cStar:ℂ)*dispersionModel S β u*squarefreeModelMass Φ A)‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  let hv : UniformLogWeights (fun _ : Unit => Φ) := uniformLogWeights_constant Φ hΦ hΦpos hΦ'
  obtain ⟨K,hK,herror⟩ := hv.active_mixedMassModel_error
  obtain ⟨M,hM,hcoeff⟩ := stopped_interval_energy (ι := ι) hξ hξz
  have hcs : 0 < cStar := cStar_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D := 18*(2:ℝ)^(1/6:ℝ)*M
  let E := cStar*K*D^2/Real.log 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨E+1,by positivity,?_⟩
  filter_upwards [hcoeff,(tendsto_rpow_atTop hκ).eventually_ge_atTop 1,
    eventually_ge_atTop (Real.exp 1)] with X hcoeff hlarge hX
  intro δ b A u hδ hδone hbX hbXhi hA W hW e j₀ k₀ h Z Q early hj hR
  dsimp only
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let R := min (X^ξ) (geometricBinLower (1+δ) X h)
  have hL1 : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hL1
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hbp : 0 < b := zero_lt_one.trans_le (hlarge.trans hbX)
  have hRp : 0 < R := (pow_pos hLp (k+1)).trans_le hR
  have hS (a : Eisenstein) (ha : a ∈ S) := stoppedIntervalSupport_spec X (b/2) b e ha
  have hc : ∀ a ∈ S, ‖β a‖ ≤ M := (hcoeff W hW _ 0 (b/2) b e hbp.le hbXhi).1
  have hAbs : 0 ≤ dispersionAbsoluteModel S β := dispersionAbsoluteModel_nonneg S β
  have hm : dispersionAbsoluteModel S β ≤ D*b^(5/6:ℝ) :=
    bounded_annular_absolute_model S β hbp hM.le (fun a ha =>
      ⟨(hS a ha).1,(Finset.mem_filter.mp ha).2.2.2.1.le,(hS a ha).2.2⟩) hc
  have hcard (a : Eisenstein) (ha : a ∈ S) (_hz : β a ≠ 0) :
      ((primaryPrimeFactors a).card:ℝ) ≤ Real.log X/Real.log 2 :=
    (primary_prime_factors_card_log (hS a ha).1).trans
      (div_le_div_of_nonneg_right (Real.log_le_log
        (norm_pos_of_ne_zero (primary_ne_zero (hS a ha).1))
        ((hS a ha).2.2.trans hbXhi)) (Real.log_pos (by norm_num)).le)
  have hr (a : Eisenstein) (_ha : a ∈ S) (hz : β a ≠ 0)
      (p : Eisenstein) (hp : p ∈ primaryPrimeFactors a) : R ≤ norm p :=
    stoppedRowCoefficient_early_roughness X (X^ξ) (X^(2/5:ℝ)) 0 (1+δ) Z Q W
      (Real.rpow_pos_of_pos hXp _) (Real.rpow_le_rpow_of_exponent_le hX1 hξz)
      (by linarith) (by linarith) j₀ k₀ h early hj hz
      (primaryPrimeFactor_spec (hS a _ha).1 hp).1 (primaryPrimeFactor_spec (hS a _ha).1 hp).2
  have he := herror () S β u A R (Real.log X/Real.log 2) hA hRp (by positivity)
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) hcard hr
  have hlog : Real.log X/R ≤ 1/(Real.log X)^k := by
    apply (div_le_div_of_nonneg_left hLp.le (pow_pos hLp _) hR).trans_eq
    rw [pow_succ]
    field_simp
  change ‖((cStar:ℂ)*star (dispersionModel S β u))*_‖ ≤ _
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos cStar_pos,norm_star]
  calc
    _ ≤ (cStar*dispersionAbsoluteModel S β)*(K*(Real.log X/Real.log 2)*A^(2/3:ℝ)/R*
        dispersionAbsoluteModel S β) := mul_le_mul
      (mul_le_mul_of_nonneg_left (norm_dispersionModel_le_absolute S β u) cStar_pos.le)
      he (_root_.norm_nonneg _) (by positivity)
    _ = (cStar*K/Real.log 2)*A^(2/3:ℝ)*(dispersionAbsoluteModel S β)^2*(Real.log X/R) := by ring
    _ ≤ (cStar*K/Real.log 2)*A^(2/3:ℝ)*(D*b^(5/6:ℝ))^2*(1/(Real.log X)^k) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (dispersionAbsoluteModel_nonneg S β) hm 2) (by positivity)
      · exact hlog
      · positivity
      · positivity
    _ = E*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
      rw [mul_pow,←Real.rpow_mul_natCast hbp.le]
      norm_num
      dsimp [E]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : E ≤ E+1)
          (Real.rpow_nonneg hA.le _)) (Real.rpow_nonneg hbp.le _))
      (pow_nonneg hLp.le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionMixedAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed term in the corrected square is the genuine Type-I sum.
No coprimality restriction is silently removed. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma moebius_sq_mul_gauss {a : Eisenstein} (ha : primary a) :
    (idealMoebius a:ℂ)^2*gauss a = gauss a := by
  rw [idealMoebius_sq_complex]
  by_cases hs : Squarefree a
  · simp only [hs,ite_true, if_true,one_mul]
  · simp only [hs,ite_false, if_false,zero_mul,gauss_eq_zero_of_not_squarefree ha hs]

lemma dispersion_mixed_finite (A B : Finset Eisenstein)
    (hA : ∀ a ∈ A, primary a) (hB : ∀ b ∈ B, primary b)
    (W β : Eisenstein → ℂ) (u : ℝ) :
    (∑ a ∈ A, (idealMoebius a:ℂ)^2*W a*gauss a*dispersionPolynomial B β u a) =
      ∑ b ∈ B, β b*normTwist u b*(∑ a ∈ A, W a*gauss (a*b)) := by
  simp_rw [dispersionPolynomial,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  rw [gauss_mul (hA a ha) (hB b hb)]
  have hm := moebius_sq_mul_gauss (hA a ha)
  calc
    _ = W a*(β b*normTwist u b)*((idealMoebius a:ℂ)^2*gauss a)*
        gauss b*star (cubicSymbol b a) := by ring
    _ = _ := by rw [hm]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CorrectedSquareExpansion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual correction model and mixed term in the positive square.
Only its first term is enlarged by the square-divisor majorant. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma correction_model_square {a : Eisenstein} (ha : primary a) (w : ℝ) (s : ℂ) :
    (idealMoebius a:ℝ)^2*w*
      ‖(cStar:ℂ)*star (gauss a)*((norm a^(-1/6:ℝ):ℝ):ℂ)*s‖^2 =
    (cStar^2*‖s‖^2)*((idealMoebius a:ℝ)^2*w*norm a^(-1/3:ℝ)) := by
  by_cases hsf : Squarefree a
  · have hp : (norm a^(-1/6:ℝ))^2 = norm a^(-1/3:ℝ) := by
      rw [←Real.rpow_natCast (norm a^(-1/6:ℝ)) 2,←Real.rpow_mul (norm_nonneg a)]
      norm_num
    rw [idealMoebius_sq,ite_eq_left hsf]
    simp only [norm_mul,norm_star,norm_gauss ha,ite_eq_left hsf,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos cStar_pos,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg a) _),mul_one,one_mul,mul_pow,hp]
    ring
  · rw [idealMoebius_sq,ite_eq_right hsf]
    simp

lemma correction_mixed_real (a : Eisenstein) (w : ℝ) (s f : ℂ) :
    (idealMoebius a:ℝ)^2*w*
      (star f*((cStar:ℂ)*star (gauss a)*((norm a^(-1/6:ℝ):ℝ):ℂ)*s)).re =
    ((cStar:ℂ)*star s*((idealMoebius a:ℂ)^2*(w:ℂ)*gauss a*
      ((norm a^(-1/6:ℝ):ℝ):ℂ)*f)).re := by
  calc
    _ = ((((idealMoebius a:ℝ)^2*w:ℝ):ℂ)*
        (star f*((cStar:ℂ)*star (gauss a)*((norm a^(-1/6:ℝ):ℝ):ℂ)*s))).re := by
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    _ = (star ((cStar:ℂ)*star s*((idealMoebius a:ℂ)^2*(w:ℂ)*gauss a*
        ((norm a^(-1/6:ℝ):ℝ):ℂ)*f))).re := by
      congr 1
      simp only [star_mul,star_pow,star_star]
      push_cast
      simp; ring
    _ = _ := by rfl

theorem corrected_dispersion_finite_majorant (A C B : Finset Eisenstein)
    (hA : ∀ a ∈ A, primary a) (hC : ∀ c ∈ C, primary c) (h1 : 1 ∈ C)
    (W : Eisenstein → ℝ) (hW : ∀ a ∈ A, 0 ≤ W a)
    (β : Eisenstein → ℂ) (u : ℝ) :
    (∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*‖correctedDispersionPolynomial B β u a‖^2) ≤
      (∑ a ∈ A, (truncatedSquareDivisorSum C a)^2*W a*‖dispersionPolynomial B β u a‖^2)-
      2*((cStar:ℂ)*star (dispersionModel B β u)*
        (∑ a ∈ A, (idealMoebius a:ℂ)^2*(W a:ℂ)*gauss a*
          ((norm a^(-1/6:ℝ):ℝ):ℂ)*dispersionPolynomial B β u a)).re+
      (cStar^2*‖dispersionModel B β u‖^2)*
        ∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*norm a^(-1/3:ℝ) := by
  have hh := corrected_squarefree_majorant A C hC h1 W hW
    (dispersionPolynomial B β u)
    (fun a => (cStar:ℂ)*star (gauss a)*((norm a^(-1/6:ℝ):ℝ):ℂ)*dispersionModel B β u)
  change (∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*‖correctedDispersionPolynomial B β u a‖^2) ≤ _ at hh
  apply hh.trans_eq
  have hm : (∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*
      ‖(cStar:ℂ)*star (gauss a)*((norm a^(-1/6:ℝ):ℝ):ℂ)*dispersionModel B β u‖^2) =
      (cStar^2*‖dispersionModel B β u‖^2)*
        ∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*norm a^(-1/3:ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a ha => correction_model_square (hA a ha) _ _)
  have hx : (∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*
      (star (dispersionPolynomial B β u a)*
        ((cStar:ℂ)*star (gauss a)*((norm a^(-1/6:ℝ):ℝ):ℂ)*dispersionModel B β u)).re) =
      ((cStar:ℂ)*star (dispersionModel B β u)*
        (∑ a ∈ A, (idealMoebius a:ℂ)^2*(W a:ℂ)*gauss a*
          ((norm a^(-1/6:ℝ):ℝ):ℂ)*dispersionPolynomial B β u a)).re := by
    rw [Finset.mul_sum,Complex.re_sum]
    exact Finset.sum_congr rfl (fun a _ => correction_mixed_real a _ _ _)
  rw [hm,hx]


/-- The three genuine model terms cancel after the positive and mixed
terms have each been identified with the same squarefree mass. -/
theorem corrected_dispersion_finite_error (A C B : Finset Eisenstein)
    (hA : ∀ a ∈ A, primary a) (hC : ∀ c ∈ C, primary c) (h1 : 1 ∈ C)
    (W : Eisenstein → ℝ) (hW : ∀ a ∈ A, 0 ≤ W a)
    (β : Eisenstein → ℂ) (u E₁ E₂ : ℝ)
    (hpositive : |(∑ a ∈ A, (truncatedSquareDivisorSum C a)^2*W a*
        ‖dispersionPolynomial B β u a‖^2)-
      (cStar^2*‖dispersionModel B β u‖^2)*
        (∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*norm a^(-1/3:ℝ))| ≤ E₁)
    (hmixed : ‖(cStar:ℂ)*star (dispersionModel B β u)*
        (∑ a ∈ A, (idealMoebius a:ℂ)^2*(W a:ℂ)*gauss a*
          ((norm a^(-1/6:ℝ):ℝ):ℂ)*dispersionPolynomial B β u a)-
      (((cStar^2*‖dispersionModel B β u‖^2)*
        (∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*norm a^(-1/3:ℝ)):ℝ):ℂ)‖ ≤ E₂) :
    (∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*‖correctedDispersionPolynomial B β u a‖^2) ≤
      E₁+2*E₂ := by
  apply (corrected_dispersion_finite_majorant A C B hA hC h1 W hW β u).trans
  have hp := (abs_le.mp hpositive).2
  have hm := (abs_le.mp ((Complex.abs_re_le_norm _).trans hmixed)).1
  simp only [Complex.sub_re,Complex.ofReal_re] at hm
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteDispersionWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compactly supported variance and model are exactly finite sums.
These identities transfer the analytic estimates into the corrected square. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefreeModelMass_eq_sum (W : ℝ → ℂ) {A R F : ℝ}
    (hA : 0 < A) (hRF : R*A ≤ F) (hcut : ∀ x, R < x → W x = 0) :
    squarefreeModelMass W A = ∑ a ∈ primaryElementBall F,
      (idealMoebius a:ℂ)^2*W (norm a/A)*((norm a^(-1/3:ℝ):ℝ):ℂ) := by
  unfold squarefreeModelMass
  calc
    _ = ∑ a ∈ primaryElementBall F, if primary a then
        (idealMoebius a:ℂ)^2*W (norm a/A)*((norm a^(-1/3:ℝ):ℝ):ℂ) else 0 := by
      apply tsum_eq_sum
      intro a ha
      by_cases hp : primary a
      · have hn : R < norm a/A := (lt_div_iff₀ hA).mpr
          (hRF.trans_lt (lt_of_not_ge (fun hn => ha (mem_primaryElementBall.mpr ⟨hp,hn⟩))))
        simp only [hcut _ hn,mul_zero,zero_mul,ite_self]
      · simp only [hp,ite_false, if_false]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [ite_eq_left (mem_primaryElementBall.mp ha).1]

lemma sievedDispersionVariance_eq_sum (C B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) {A R F : ℝ} (hA : 0 < A) (hRF : R*A ≤ F)
    (hcut : ∀ x, R < x → W x = 0) :
    sievedDispersionVariance C B β u W A =
      ∑ a ∈ primaryElementBall F, (((truncatedSquareDivisorSum C a)^2:ℝ):ℂ)*
        W (norm a/A)*((‖dispersionPolynomial B β u a‖^2:ℝ):ℂ) := by
  unfold sievedDispersionVariance
  calc
    _ = ∑ a ∈ primaryElementBall F, if primary a then
        (((truncatedSquareDivisorSum C a)^2:ℝ):ℂ)*W (norm a/A)*
          ((‖dispersionPolynomial B β u a‖^2:ℝ):ℂ) else 0 := by
      apply tsum_eq_sum
      intro a ha
      by_cases hp : primary a
      · have hn : R < norm a/A := (lt_div_iff₀ hA).mpr
          (hRF.trans_lt (lt_of_not_ge (fun hn => ha (mem_primaryElementBall.mpr ⟨hp,hn⟩))))
        simp only [hcut _ hn,mul_zero,zero_mul,ite_self]
      · simp only [hp,ite_false, if_false]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [ite_eq_left (mem_primaryElementBall.mp ha).1]

lemma squarefreeModelMass_ofReal (V : ℝ → ℝ) {A R F : ℝ}
    (hA : 0 < A) (hRF : R*A ≤ F) (hcut : ∀ x, R < x → V x = 0) :
    squarefreeModelMass (fun x => (V x:ℂ)) A =
      ((∑ a ∈ primaryElementBall F, (idealMoebius a:ℝ)^2*V (norm a/A)*
        norm a^(-1/3:ℝ):ℝ):ℂ) := by
  rw [squarefreeModelMass_eq_sum _ hA hRF (fun x hx => by rw [hcut x hx]; rfl),Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a ha
  push_cast; rfl

lemma sievedDispersionVariance_ofReal (C B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℝ) {A R F : ℝ} (hA : 0 < A) (hRF : R*A ≤ F)
    (hcut : ∀ x, R < x → V x = 0) :
    sievedDispersionVariance C B β u (fun x => (V x:ℂ)) A =
      ((∑ a ∈ primaryElementBall F, (truncatedSquareDivisorSum C a)^2*V (norm a/A)*
        ‖dispersionPolynomial B β u a‖^2:ℝ):ℂ) := by
  rw [sievedDispersionVariance_eq_sum C B β u _ hA hRF (fun x hx => by rw [hcut x hx]; rfl),
    Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a ha
  push_cast; rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CorrectedSquareMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine squarefree corrected variance, with its exact finite
support reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma correctedSquareMass_eq_sum (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℝ) {A R F : ℝ} (hA : 0 < A) (hRF : R*A ≤ F)
    (hcut : ∀ x, R < x → V x = 0) :
    correctedSquareMass S β u V A = ∑ a ∈ primaryElementBall F,
      (idealMoebius a:ℝ)^2*V (norm a/A)*‖correctedDispersionPolynomial S β u a‖^2 := by
  unfold correctedSquareMass
  calc
    _ = ∑ a ∈ primaryElementBall F, if primary a then
        (idealMoebius a:ℝ)^2*V (norm a/A)*‖correctedDispersionPolynomial S β u a‖^2 else 0 := by
      apply tsum_eq_sum
      intro a ha
      by_cases hp : primary a
      · have hn : R < norm a/A := (lt_div_iff₀ hA).mpr
          (hRF.trans_lt (lt_of_not_ge (fun hn => ha (mem_primaryElementBall.mpr ⟨hp,hn⟩))))
        simp only [hcut _ hn,mul_zero,zero_mul,ite_self]
      · simp only [hp,ite_false, if_false]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [ite_eq_left (mem_primaryElementBall.mp ha).1]

lemma correctedSquareMass_nonneg (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x) (A : ℝ) :
    0 ≤ correctedSquareMass S β u V A := by
  apply tsum_nonneg
  intro a
  split_ifs
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (hV _)) (sq_nonneg _)
  · exact le_rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CorrectedBilinearMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cauchy--Schwarz with the true squarefree corrected mass. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_gauss_sq_eq_moebius_sq {a : Eisenstein} (ha : primary a) :
    ‖gauss a‖^2 = (idealMoebius a:ℝ)^2 := by
  rw [norm_gauss ha,idealMoebius_sq]
  split_ifs <;> norm_num

theorem corrected_bilinear_mass_bound_sq (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) (hP : ∀ a ∈ P, primary a)
    (hB : ∀ b ∈ B, primary b) (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    {A R : ℝ} (hA : 0 < A) (hcut : ∀ x, R < x → V x = 0)
    (hPV : ∀ a ∈ P, 1 ≤ V (norm a/A)) :
    ‖(∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*normTwist u (a*b))-
      (cStar:ℂ)*dispersionModel B β u*
        (∑ a ∈ P, α a*normTwist u a*(if Squarefree a then (1:ℂ) else 0)*
          ((norm a^(-1/6:ℝ):ℝ):ℂ))‖^2 ≤
      (∑ a ∈ P, ‖α a‖^2)*correctedSquareMass B β u V A := by
  rw [corrected_bilinear_identity P B α β u hP hB]
  have hsub : P ⊆ primaryElementBall (R*A) := by
    intro a ha
    refine mem_primaryElementBall.mpr ⟨hP a ha,?_⟩
    apply (div_le_iff₀ hA).mp
    by_contra h
    have hz := hcut (norm a/A) (lt_of_not_ge h)
    have hv := hPV a ha
    rw [hz] at hv
    norm_num at hv
  have hrows : (∑ a ∈ P, ‖normTwist u a*gauss a*
      correctedDispersionPolynomial B β u a‖^2) ≤ correctedSquareMass B β u V A := by
    rw [correctedSquareMass_eq_sum B β u V hA le_rfl hcut]
    apply (Finset.sum_le_sum (g := fun a => (idealMoebius a:ℝ)^2*V (norm a/A)*
      ‖correctedDispersionPolynomial B β u a‖^2) ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (hV _)) (sq_nonneg _)))
    intro a ha
    simp only [norm_mul,norm_normTwist,one_mul,mul_pow,
      norm_gauss_sq_eq_moebius_sq (hP a ha)]
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (sq_nonneg _) (hPV a ha)) (sq_nonneg _)
  calc
    _ = ‖∑ a ∈ P, α a*(normTwist u a*gauss a*
        correctedDispersionPolynomial B β u a)‖^2 := by
      congr 2
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ (∑ a ∈ P, ‖α a‖^2)*
        ∑ a ∈ P, ‖normTwist u a*gauss a*correctedDispersionPolynomial B β u a‖^2 :=
      complex_bilinear_rows_sq P α _
    _ ≤ _ := mul_le_mul_of_nonneg_left hrows (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CorrectedBilinearScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem corrected_bilinear_log_saving (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) (hP : ∀ a ∈ P, primary a)
    (hB : ∀ b ∈ B, primary b) (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    {A R L z M K : ℝ} (hA : 0 < A) (hL : 0 < L) (hz : 0 < z)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hcut : ∀ x, R < x → V x = 0)
    (hPV : ∀ a ∈ P, 1 ≤ V (norm a/A)) (k d : ℕ)
    (henergy : (∑ a ∈ P, ‖α a‖^2) ≤ M*A*z^d)
    (hmass : correctedSquareMass B β u V A ≤
      K*A^(2/3:ℝ)*L^(5/3:ℝ)/z^(2*k+d)) :
    ‖correctedBilinearSum P B α β u‖ ≤
      Real.sqrt (M*K)*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k := by
  exact bilinear_error_log_saving hM hK hA hL hz k d
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (correctedSquareMass_nonneg B β u V hV A)
    (corrected_bilinear_mass_bound_sq P B α β u hP hB V hV hA hcut hPV)
    henergy hmass

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BilinearKernelIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The factored correction and the original squarefree product kernel
are related by the explicit shared-prime contribution. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma centered_bilinear_eq_correction_add_overlap (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) (hP : ∀ a ∈ P, primary a)
    (hB : ∀ b ∈ B, primary b ∧ Squarefree b) :
    (∑ a ∈ P, ∑ b ∈ B, α a*β b*centeredGauss (a*b)*normTwist u (a*b)) =
      correctedBilinearSum P B α β u + modelOverlap P B α β u := by
  unfold correctedBilinearSum modelOverlap dispersionModel
  have hm : ((cStar:ℂ)*(∑ b ∈ B, β b*normTwist u b*((norm b^(-1/6:ℝ):ℝ):ℂ)))*
      (∑ a ∈ P, α a*normTwist u a*(if Squarefree a then (1:ℂ) else 0)*
        ((norm a^(-1/6:ℝ):ℝ):ℂ)) =
      ∑ a ∈ P, ∑ b ∈ B, ((cStar:ℂ)*(β b*normTwist u b*((norm b^(-1/6:ℝ):ℝ):ℂ)))*
        (α a*normTwist u a*(if Squarefree a then (1:ℂ) else 0)*((norm a^(-1/6:ℝ):ℝ):ℂ)) := by
    simp only [Finset.mul_sum,Finset.sum_mul]
  rw [hm]
  simp only [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hna := norm_pos_of_ne_zero (primary_ne_zero (hP a ha))
  have hnb := norm_pos_of_ne_zero (primary_ne_zero (hB b hb).1)
  rw [centeredGauss,normTwist_mul u (primary_ne_zero (hP a ha))
    (primary_ne_zero (hB b hb).1),norm_mul_eq,Real.mul_rpow hna.le hnb.le]
  have hμ : (idealMoebius (a*b):ℂ)^2 =
      if IsCoprime a b then (idealMoebius a:ℂ)^2 else 0 := by
    simpa only [mul_comm b a,isCoprime_comm] using
      idealMoebius_sq_mul_of_squarefree (hB b hb).2 a
  rw [hμ,←idealMoebius_sq_complex]
  push_cast
  split_ifs <;> ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BipartiteEnergy
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A two-sided incidence bound with independent coefficient energies. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma bipartite_sum_sq_le {α β : Type*} (P : Finset α) (B : Finset β)
    (R : α → β → Prop) [DecidableRel R] (a : α → ℝ) (b : β → ℝ) {M N : ℝ}
    (hM : 0 ≤ M) (_hN : 0 ≤ N)
    (hrow : ∀ x ∈ P, ((B.filter (R x)).card:ℝ) ≤ M)
    (hcol : ∀ y ∈ B, ((P.filter (fun x => R x y)).card:ℝ) ≤ N) :
    (∑ x ∈ P, ∑ y ∈ B, if R x y then a x*b y else 0)^2 ≤
      (M*∑ x ∈ P, (a x)^2)*(N*∑ y ∈ B, (b y)^2) := by
  let E := (P ×ˢ B).filter (fun p => R p.1 p.2)
  have hs : (∑ p ∈ E, a p.1*b p.2) =
      ∑ x ∈ P, ∑ y ∈ B, if R x y then a x*b y else 0 := by
    rw [Finset.sum_filter,Finset.sum_product]
  have hx : (∑ p ∈ E, (a p.1)^2) ≤ M*∑ x ∈ P, (a x)^2 := by
    rw [Finset.sum_filter,Finset.sum_product,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hrow x hx) (sq_nonneg _)
  have hy : (∑ p ∈ E, (b p.2)^2) ≤ N*∑ y ∈ B, (b y)^2 := by
    rw [Finset.sum_filter,Finset.sum_product,Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y hy
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hcol y hy) (sq_nonneg _)
  rw [←hs]
  exact (Finset.sum_mul_sq_le_sq_mul_sq E _ _).trans
    (mul_le_mul hx hy (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg hM (Finset.sum_nonneg fun _ _ => sq_nonneg _)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelOverlapBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative removal of the shared-prime terms in the factored model. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_modelOverlap_le (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (u : ℝ) {A L : ℝ} (hA : 0 < A) (hL : 0 < L)
    (hP : ∀ a ∈ P, A ≤ norm a) (hB : ∀ b ∈ B, L ≤ norm b) :
    ‖modelOverlap P B α β u‖ ≤ cStar*A^(-1/6:ℝ)*L^(-1/6:ℝ)*
      ∑ a ∈ P, ∑ b ∈ B, if ¬IsCoprime a b then ‖α a‖*‖β b‖ else 0 := by
  unfold modelOverlap
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  by_cases hcop : IsCoprime a b
  · simp only [hcop,ite_true, if_true,not_true_eq_false,ite_false, if_false,norm_zero,mul_zero,le_refl]
  · simp only [hcop,ite_false, if_false,not_false_eq_true,ite_true, if_true,norm_mul,norm_pow,
      norm_normTwist,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos cStar_pos,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    have hm : ‖(idealMoebius a:ℂ)‖^2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_idealMoebius_le_one a) 2
    have hpa : norm a^(-1/6:ℝ) ≤ A^(-1/6:ℝ) :=
      Real.rpow_le_rpow_of_nonpos hA (hP a ha) (by norm_num)
    have hpb : norm b^(-1/6:ℝ) ≤ L^(-1/6:ℝ) :=
      Real.rpow_le_rpow_of_nonpos hL (hB b hb) (by norm_num)
    have hcs := cStar_pos
    have hna := norm_nonneg a
    have hnb := norm_nonneg b
    calc
      _ ≤ cStar*‖α a‖*‖β b‖*1*A^(-1/6:ℝ)*L^(-1/6:ℝ) := by gcongr
      _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OverlapScale
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary powers and logarithmic absorption for model overlap. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma negative_sixth_square_scale {x : ℝ} (hx : 0 < x) :
    (x^(-1/6:ℝ))^2*x*x = x^(5/3:ℝ) := by
  calc
    _ = (x^(-1/6:ℝ))^2*x^2 := by ring
    _ = _ := by
      rw [←Real.rpow_natCast (x^(-1/6:ℝ)) 2,←Real.rpow_mul hx.le,
        ←Real.rpow_natCast x 2,←Real.rpow_add hx]
      norm_num

lemma model_overlap_scale {A L : ℝ} (hA : 0 < A) (hL : 0 < L)
    (M Q C₁ C₂ n z D : ℝ) (d a : ℕ) :
    (cStar*A^(-1/6:ℝ)*L^(-1/6:ℝ))^2*
      ((C₁*L*(M*A*z^d))*(n*(18*(Q*A)/D)*(C₂*L*z^a))) =
      (cStar^2*C₁*n*18*Q*C₂)*M*A^(5/3:ℝ)*L^(5/3:ℝ)*z^(d+a)/D := by
  calc
    _ = (cStar^2*C₁*n*18*Q*C₂)*M*
        ((A^(-1/6:ℝ))^2*A*A)*((L^(-1/6:ℝ))^2*L*L)*z^(d+a)/D := by
      rw [pow_add]
      ring
    _ = _ := by rw [negative_sixth_square_scale hA,negative_sixth_square_scale hL]

lemma norm_le_bilinear_of_square {x : ℂ} {C A L z : ℝ}
    (hC : 0 ≤ C) (hA : 0 < A) (hL : 0 < L) (hz : 0 < z) (k : ℕ)
    (h : ‖x‖^2 ≤ C*A^(5/3:ℝ)*L^(5/3:ℝ)/z^(2*k)) :
    ‖x‖ ≤ Real.sqrt C*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k := by
  have hp (t : ℝ) (ht : 0 < t) : (t^(5/6:ℝ))^2 = t^(5/3:ℝ) := by
    rw [←Real.rpow_natCast (t^(5/6:ℝ)) 2,←Real.rpow_mul ht.le]
    norm_num
  have he : (Real.sqrt C*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k)^2 =
      C*A^(5/3:ℝ)*L^(5/3:ℝ)/z^(2*k) := by
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hC,hp A hA,hp L hL]
    simp only [←pow_mul,Nat.mul_comm]
  rw [←he] at h
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (by positivity)).mp h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBilinearOverlap
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shared-prime incidence for the literal support. Inactive stopped
coefficients contribute zero, so only active rows require roughness. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma active_noncoprime_bipartite_energy (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) {Y R Q : ℝ} (hY : 0 ≤ Y) (hR : 0 < R) (hQ : 0 ≤ Q)
    (hP : ∀ a ∈ P, a ≠ 0 ∧ norm a ≤ Y)
    (hB : ∀ b ∈ B, primary b ∧ Squarefree b)
    (hn : ∀ b ∈ B, β b ≠ 0 → ((primaryPrimeFactors b).card:ℝ) ≤ Q)
    (hrough : ∀ b ∈ B, β b ≠ 0 → ∀ p ∈ primaryPrimeFactors b, R ≤ norm p) :
    (∑ a ∈ P, ∑ b ∈ B, if ¬IsCoprime a b then ‖α a‖*‖β b‖ else 0)^2 ≤
      ((B.card:ℝ)*∑ a ∈ P, ‖α a‖^2)*
        (Q*(18*Y/R)*∑ b ∈ B, ‖β b‖^2) := by
  let rel := fun a b : Eisenstein => ¬IsCoprime a b ∧ β b ≠ 0
  have hr (a : Eisenstein) (_ha : a ∈ P) :
      ((B.filter (rel a)).card:ℝ) ≤ B.card := by
    exact_mod_cast Finset.card_filter_le B (rel a)
  have hc (b : Eisenstein) (hb : b ∈ B) :
      ((P.filter (fun a => rel a b)).card:ℝ) ≤ Q*(18*Y/R) := by
    by_cases hz : β b = 0
    · simp only [rel,hz,ne_eq,not_true_eq_false,and_false,Finset.filter_false,
        Finset.card_empty,Nat.cast_zero]
      positivity
    · have he : P.filter (fun a => rel a b) = P.filter (fun a => ¬IsCoprime b a) := by
        ext a
        simp only [Finset.mem_filter,rel,hz,ne_eq,not_false_eq_true,and_true,isCoprime_comm]
      rw [he]
      exact (noncoprime_row_card_le P hY hR hP (hB b hb).1 (hB b hb).2
        (hrough b hb hz)).trans
          (mul_le_mul_of_nonneg_right (hn b hb hz) (by positivity))
  have he := bipartite_sum_sq_le P B rel (fun a => ‖α a‖) (fun b => ‖β b‖)
    (Nat.cast_nonneg _) (show 0 ≤ Q*(18*Y/R) by positivity) hr hc
  have hs : (∑ a ∈ P, ∑ b ∈ B, if rel a b then ‖α a‖*‖β b‖ else 0) =
      ∑ a ∈ P, ∑ b ∈ B, if ¬IsCoprime a b then ‖α a‖*‖β b‖ else 0 := by
    apply Finset.sum_congr rfl
    intro a _ha
    apply Finset.sum_congr rfl
    intro b _hb
    by_cases hz : β b = 0 <;> simp [rel,hz]
  rwa [hs] at he

lemma active_modelOverlap_norm_sq_le (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (u : ℝ) {A L Y R Q : ℝ} (hA : 0 < A) (hL : 0 < L)
    (hY : 0 ≤ Y) (hR : 0 < R) (hQ : 0 ≤ Q)
    (hP : ∀ a ∈ P, a ≠ 0 ∧ A ≤ norm a ∧ norm a ≤ Y)
    (hB : ∀ b ∈ B, primary b ∧ Squarefree b ∧ L ≤ norm b)
    (hn : ∀ b ∈ B, β b ≠ 0 → ((primaryPrimeFactors b).card:ℝ) ≤ Q)
    (hrough : ∀ b ∈ B, β b ≠ 0 → ∀ p ∈ primaryPrimeFactors b, R ≤ norm p) :
    ‖modelOverlap P B α β u‖^2 ≤ (cStar*A^(-1/6:ℝ)*L^(-1/6:ℝ))^2*
      (((B.card:ℝ)*∑ a ∈ P, ‖α a‖^2)*(Q*(18*Y/R)*∑ b ∈ B, ‖β b‖^2)) := by
  have hh := norm_modelOverlap_le P B α β u hA hL
    (fun a ha => (hP a ha).2.1) (fun b hb => (hB b hb).2.2)
  have he := active_noncoprime_bipartite_energy P B α β hY hR hQ
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.2⟩)
    (fun b hb => ⟨(hB b hb).1,(hB b hb).2.1⟩) hn hrough
  apply (pow_le_pow_left₀ (_root_.norm_nonneg _) hh 2).trans
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left he (sq_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SieveResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The residue sum after squarefree majorization

The actual collected coefficients agree with Möbius below the truncation.
Their uniformly convergent norm series therefore differs from the true
Möbius residue by `O(D⁻¹ᐟ²)`.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefreeTruncation_spec (D : ℝ) :
    ∀ c ∈ squarefreeDivisorTruncation D, primary c ∧ Squarefree c := by
  intro c hc
  exact ⟨(mem_squarefreeDivisorTruncation.mp hc).1,(mem_squarefreeDivisorTruncation.mp hc).2.1⟩

lemma squarefreeSieveCoefficient_zero {D : ℝ} {e : Eisenstein} (hs : ¬Squarefree e) :
    collectedSquarefreeSieveCoefficient (squarefreeDivisorTruncation D) e = 0 := by
  by_contra hn
  obtain ⟨a,ha,b,hb,hab⟩ := collectedSieveCoefficient_nonzero _ e hn
  apply hs
  rw [← hab]
  exact primarySquarefreeJoin_squarefree (squarefreeTruncation_spec D a ha).1
    (squarefreeTruncation_spec D b hb).1

lemma sieveResidueTerm_eq_of_norm_le {D : ℝ} {e : Eisenstein} (h : norm e ≤ D) :
    squarefreeSieveResidueTerm D e = moebiusResidueTerm e := by
  by_cases hp : primary e
  · simp only [squarefreeSieveResidueTerm,moebiusResidueTerm,hp,ite_true, if_true]
    by_cases hs : Squarefree e
    · rw [squarefreeSieveCoefficient_small hp hs h]
    · rw [squarefreeSieveCoefficient_zero hs]
      have hm : idealMoebius e = 0 := by simp [idealMoebius,UniqueFactorizationMonoid.moebius,hs]
      rw [hm]
      simp
  · simp [squarefreeSieveResidueTerm,moebiusResidueTerm,hp]

/-- Uniform pointwise majorant with the entire discrepancy beyond `D`. -/
theorem sieveResidue_difference_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℝ, ∀ e : Eisenstein,
      |squarefreeSieveResidueTerm D e - moebiusResidueTerm e| ≤
        if D < norm e then K*norm e^(-(7/4:ℝ)) else 0 := by
  obtain ⟨K,hK,hbound⟩ := collectedSieveCoefficient_small_power (ε := (1/4:ℝ)) (by norm_num)
  refine ⟨K+1,by linarith,?_⟩
  intro D e
  by_cases ht : D < norm e
  · rw [ite_eq_left ht]
    by_cases hp : primary e
    · have hn : 0 < norm e := norm_pos_of_ne_zero (primary_ne_zero hp)
      have hpow : 1 ≤ norm e^(1/4:ℝ) :=
        Real.one_le_rpow (one_le_norm (primary_ne_zero hp)) (by norm_num)
      have hm := abs_idealMoebius_real_le_one e
      have hc := hbound (squarefreeDivisorTruncation D) (squarefreeTruncation_spec D) e
      have heq : norm e^(1/4:ℝ)/(norm e)^2 = norm e^(-(7/4:ℝ)) := by
        rw [← Real.rpow_natCast (norm e) 2,← Real.rpow_sub hn]
        congr 1
        norm_num
      simp only [squarefreeSieveResidueTerm,moebiusResidueTerm,hp,ite_true, if_true,← sub_div,
        abs_div,abs_of_nonneg (sq_nonneg (norm e))]
      calc
        _ ≤ (|collectedSquarefreeSieveCoefficient (squarefreeDivisorTruncation D) e|+
            |(idealMoebius e : ℝ)|)/(norm e)^2 :=
          div_le_div_of_nonneg_right (abs_sub _ _) (sq_nonneg _)
        _ ≤ ((K+1)*norm e^(1/4:ℝ))/(norm e)^2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          nlinarith
        _ = _ := by rw [mul_div_assoc,heq]
    · simp only [squarefreeSieveResidueTerm,moebiusResidueTerm,hp,ite_false, if_false,
        sub_self,abs_zero]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg (norm_nonneg e) _)
  · rw [ite_eq_right ht,sieveResidueTerm_eq_of_norm_le (le_of_not_gt ht)]
    simp

lemma moebiusResidueTerm_abs_le (e : Eisenstein) :
    |moebiusResidueTerm e| ≤ norm e^(-(2:ℝ)) := by
  by_cases hp : primary e
  · have hn := norm_pos_of_ne_zero (primary_ne_zero hp)
    simp only [moebiusResidueTerm,hp,ite_true, if_true,abs_div,abs_of_nonneg (sq_nonneg (norm e))]
    calc
      _ ≤ 1/(norm e)^2 :=
        div_le_div_of_nonneg_right (abs_idealMoebius_real_le_one e) (sq_nonneg _)
      _ = _ := by rw [Real.rpow_neg hn.le,Real.rpow_two,one_div]
  · simp only [moebiusResidueTerm,hp,ite_false, if_false,abs_zero]
    exact Real.rpow_nonneg (norm_nonneg e) _

lemma summable_moebiusResidueTerm : Summable moebiusResidueTerm := by
  apply (summable_eisenstein_norm_rpow (s := 2) (by norm_num)).of_norm_bounded
  intro e
  simpa only [Real.norm_eq_abs] using moebiusResidueTerm_abs_le e

lemma summable_sieveResidue_difference (D : ℝ) :
    Summable (fun e => squarefreeSieveResidueTerm D e - moebiusResidueTerm e) := by
  obtain ⟨K,_,hK⟩ := sieveResidue_difference_bound
  apply ((summable_eisenstein_norm_rpow (s := (7/4:ℝ)) (by norm_num)).mul_left K).of_norm_bounded
  intro e
  rw [Real.norm_eq_abs]
  apply (hK D e).trans
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (le_of_lt ‹0 < K›) (Real.rpow_nonneg (norm_nonneg e) _)

lemma summable_squarefreeSieveResidueTerm (D : ℝ) :
    Summable (squarefreeSieveResidueTerm D) := by
  have h := (summable_sieveResidue_difference D).add summable_moebiusResidueTerm
  simpa only [sub_add_cancel] using h

/-- The sieve residue has a uniform square-root truncation error. -/
theorem sieveResidue_difference_le :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, 0 < D →
      |(∑' e : Eisenstein, squarefreeSieveResidueTerm D e) -
        (∑' e : Eisenstein, moebiusResidueTerm e)| ≤ C*D^(-(1/2:ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := sieveResidue_difference_bound
  let Z := ∑' e : Eisenstein, norm e^(-(5/4:ℝ))
  have hZ : 0 ≤ Z := tsum_nonneg (fun e => Real.rpow_nonneg (norm_nonneg e) _)
  refine ⟨K*Z+1,by nlinarith,?_⟩
  intro D hD
  have htail : Summable (fun e : Eisenstein =>
      if D < norm e then norm e^(-(7/4:ℝ)) else 0) :=
    (summable_eisenstein_norm_rpow (s := (7/4:ℝ)) (by norm_num)).indicator _
  have hdiff := summable_sieveResidue_difference D
  have htailbound := eisenstein_norm_rpow_tail (s := (5/4:ℝ)) (t := (7/4:ℝ)) hD
    (by norm_num) (by norm_num)
  rw [show (5/4:ℝ)-7/4 = -(1/2:ℝ) by norm_num] at htailbound
  rw [← (summable_squarefreeSieveResidueTerm D).tsum_sub summable_moebiusResidueTerm]
  calc
    _ ≤ ∑' e : Eisenstein, |squarefreeSieveResidueTerm D e - moebiusResidueTerm e| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hdiff.norm
    _ ≤ ∑' e : Eisenstein, K*(if D < norm e then norm e^(-(7/4:ℝ)) else 0) := by
      apply Summable.tsum_le_tsum _ hdiff.norm (htail.mul_left K)
      intro e
      simpa only [mul_ite,mul_zero,Real.norm_eq_abs] using hbound D e
    _ = K*(∑' e : Eisenstein, if D < norm e then norm e^(-(7/4:ℝ)) else 0) := tsum_mul_left
    _ ≤ K*(D^(-(1/2:ℝ))*Z) := mul_le_mul_of_nonneg_left htailbound hK.le
    _ ≤ (K*Z+1)*D^(-(1/2:ℝ)) := by
      have hp := Real.rpow_nonneg hD.le (-(1/2:ℝ))
      nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SievedModelAssembly
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite sieve assembly and its error norm. These identities
retain the actual joined square divisors and their Möbius weights. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma collectedSieve_weighted_sum (C : Finset Eisenstein) (F : Eisenstein → ℂ) :
    (∑ d ∈ (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2),
      (collectedSquarefreeSieveCoefficient C d:ℂ)*F d) =
    ∑ c ∈ C, ∑ d ∈ C, (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*F (primarySquarefreeJoin c d) := by
  let J := fun t : Eisenstein × Eisenstein => primarySquarefreeJoin t.1 t.2
  let v := fun t : Eisenstein × Eisenstein => (idealMoebius t.1:ℂ)*(idealMoebius t.2:ℂ)
  have hf := Finset.sum_fiberwise_of_maps_to (s := C.product C) (t := (C.product C).image J)
    (g := J) (fun t ht => Finset.mem_image_of_mem J ht) (fun t => v t*F (J t))
  calc
    _ = ∑ d ∈ (C.product C).image J,
        ∑ t ∈ (C.product C).filter (fun t => J t = d), v t*F (J t) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [collectedSquarefreeSieveCoefficient,Complex.ofReal_sum,Complex.ofReal_mul,
        Complex.ofReal_intCast,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      dsimp only [v,J]
      rw [(Finset.mem_filter.mp ht).2]
    _ = ∑ t ∈ C.product C, v t*F (J t) := hf
    _ = _ := Finset.sum_product _ _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteSieveDensity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify the finite square-divisor density with the already proved
convergent Möbius residue series. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma collectedSieve_weighted_sum_real (C : Finset Eisenstein) (F : Eisenstein → ℝ) :
    (∑ d ∈ (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2),
      collectedSquarefreeSieveCoefficient C d*F d) =
    ∑ c ∈ C, ∑ d ∈ C, (idealMoebius c:ℝ)*(idealMoebius d:ℝ)*F (primarySquarefreeJoin c d) := by
  have h := collectedSieve_weighted_sum C (fun d => (F d:ℂ))
  exact_mod_cast h

lemma collectedSieve_eq_zero_off_image (C : Finset Eisenstein) {d : Eisenstein}
    (hd : d ∉ (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2)) :
    collectedSquarefreeSieveCoefficient C d = 0 := by
  by_contra hn
  obtain ⟨a,ha,b,hb,he⟩ := collectedSieveCoefficient_nonzero C d hn
  exact hd (Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,he⟩)

lemma finiteSieveDensity_eq_sum (C : Finset Eisenstein) :
    finiteSieveDensity C = ∑ d ∈ (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2),
      collectedSquarefreeSieveCoefficient C d/(norm d)^2 := by
  simpa only [finiteSieveDensity,div_eq_mul_inv] using
    (collectedSieve_weighted_sum_real C (fun d => ((norm d)^2)⁻¹)).symm

lemma finiteSieveDensity_eq_residue (D : ℝ) :
    finiteSieveDensity (squarefreeDivisorTruncation D) =
      ∑' d : Eisenstein, squarefreeSieveResidueTerm D d := by
  let C := squarefreeDivisorTruncation D
  let S := (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2)
  have hs : (∑' d : Eisenstein, squarefreeSieveResidueTerm D d) =
      ∑ d ∈ S, squarefreeSieveResidueTerm D d := by
    apply tsum_eq_sum
    intro d hd
    unfold squarefreeSieveResidueTerm
    rw [collectedSieve_eq_zero_off_image C hd]
    split_ifs <;> simp
  rw [hs,finiteSieveDensity_eq_sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hd
  have ha := squarefreeTruncation_spec D a (Finset.mem_product.mp hab).1
  have hb := squarefreeTruncation_spec D b (Finset.mem_product.mp hab).2
  simp only [squarefreeSieveResidueTerm,ite_eq_left (primarySquarefreeJoin_primary ha.1 hb.1)]

 theorem finiteSieveDensity_error : ∃ K : ℝ, 0 < K ∧ ∀ D : ℝ, 1 ≤ D →
    |finiteSieveDensity (squarefreeDivisorTruncation D)-
      (∑' d : Eisenstein, moebiusResidueTerm d)| ≤ K*D^(-(1/2:ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := sieveResidue_difference_le
  refine ⟨K,hK,?_⟩
  intro D hD
  rw [finiteSieveDensity_eq_residue]
  exact hbound D (zero_lt_one.trans_le hD)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MoebiusDensityTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary radial Möbius density converges to the same literal
residue series used by the positive square-divisor sieve. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma radialEulerPartial_one_eq (D : ℝ) :
    metaplecticRadialEulerPartial 1 D =
      ((∑ a ∈ primaryElementBall D, moebiusResidueTerm a : ℝ):ℂ) := by
  unfold metaplecticRadialEulerPartial
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hp := (mem_primaryElementBall.mp ha).1
  simp only [isCoprime_one_left,ite_true, if_true,moebiusResidueTerm,hp]
  rw [Real.rpow_neg (norm_nonneg a),Real.rpow_two]
  push_cast
  ring

lemma moebiusResidue_partial_error :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℝ, 0 < D →
      |(∑ a ∈ primaryElementBall D, moebiusResidueTerm a)-
        (∑' a : Eisenstein, moebiusResidueTerm a)| ≤ K*D^(-(1/2:ℝ)) := by
  let Z := ∑' a : Eisenstein, norm a^(-(3/2:ℝ))
  have hZ : 0 ≤ Z := tsum_nonneg (fun a => Real.rpow_nonneg (norm_nonneg a) _)
  refine ⟨Z+1,by positivity,?_⟩
  intro D hD
  let f : Eisenstein → ℝ := fun a => if a ∈ primaryElementBall D then moebiusResidueTerm a else 0
  have hf : Summable f := summable_of_ne_finset_zero
    (s := primaryElementBall D) (fun a ha => by simp only [f,ite_eq_right ha])
  have hsum : (∑' a, f a) = ∑ a ∈ primaryElementBall D, moebiusResidueTerm a := by
    calc
      _ = ∑ a ∈ primaryElementBall D, f a := tsum_eq_sum
        (fun a ha => by simp only [f,ite_eq_right ha])
      _ = _ := Finset.sum_congr rfl (fun a ha => by simp only [f,ite_eq_left ha])
  have htail := (summable_eisenstein_norm_rpow (s := 2) (by norm_num)).indicator
    (fun a => D < norm a)
  have hb (a : Eisenstein) : |f a-moebiusResidueTerm a| ≤
      if D < norm a then norm a^(-(2:ℝ)) else 0 := by
    by_cases ha : a ∈ primaryElementBall D
    · simp only [f,ha,ite_true, if_true,sub_self,abs_zero]
      split_ifs
      · exact Real.rpow_nonneg (norm_nonneg a) _
      · exact le_rfl
    · by_cases hp : primary a
      · have hn : D < norm a := lt_of_not_ge (fun hn => ha (mem_primaryElementBall.mpr ⟨hp,hn⟩))
        simpa only [f,ha,ite_false, if_false,zero_sub,abs_neg,hn,ite_true, if_true] using moebiusResidueTerm_abs_le a
      · simp only [f,ite_eq_right ha,moebiusResidueTerm,ite_eq_right hp,sub_self,abs_zero]
        split_ifs
        · exact Real.rpow_nonneg (norm_nonneg a) _
        · exact le_rfl
  rw [←hsum,←hf.tsum_sub summable_moebiusResidueTerm]
  calc
    _ ≤ ∑' a, |f a-moebiusResidueTerm a| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (hf.sub summable_moebiusResidueTerm).norm
    _ ≤ ∑' a : Eisenstein, if D < norm a then norm a^(-(2:ℝ)) else 0 :=
      Summable.tsum_le_tsum hb (hf.sub summable_moebiusResidueTerm).abs htail
    _ ≤ D^(-(1/2:ℝ))*Z := by
      simpa only [show (3/2:ℝ)-2 = -(1/2:ℝ) by norm_num] using
        eisenstein_norm_rpow_tail (s := 3/2) (t := 2) hD (by norm_num) (by norm_num)
    _ ≤ (Z+1)*D^(-(1/2:ℝ)) := by nlinarith [Real.rpow_nonneg hD.le (-(1/2:ℝ))]

lemma radialEulerPartial_one_error :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℝ, 0 < D →
      ‖metaplecticRadialEulerPartial 1 D-
        ((∑' a : Eisenstein, moebiusResidueTerm a):ℝ)‖ ≤ K*D^(-(1/2:ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := moebiusResidue_partial_error
  refine ⟨K,hK,?_⟩
  intro D hD
  rw [radialEulerPartial_one_eq,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact hbound D hD

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeMassDensity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative identification of the ordinary squarefree model mass
with the finite density in the positive variance term. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma squarefree_density_scale {A : ℝ} (hA : 1 ≤ A) {B : ℝ} (hB : 1 ≤ B) :
    (Real.sqrt (B*A))^(-(1/2:ℝ)) ≤ A^(-(1/4:ℝ)) := by
  have hAp : 0 < A := zero_lt_one.trans_le hA
  calc
    _ ≤ (Real.sqrt A)^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_nonpos
      (Real.sqrt_pos.mpr hAp) (Real.sqrt_le_sqrt (by nlinarith)) (by norm_num)
    _ = _ := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hAp.le]
      norm_num

theorem UniformLogWeights.squarefreeModelMass_density_error
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i A D, 1 ≤ A → 1 ≤ D →
      ‖squarefreeModelMass (W i) A-
        ((A^(2/3:ℝ)*(2*Real.pi/(9*Real.sqrt 3)):ℝ):ℂ)*mellin (W i) (2/3)*
          (finiteSieveDensity (squarefreeDivisorTruncation D):ℂ)‖ ≤
        K*(A^(5/12:ℝ)+A^(2/3:ℝ)*D^(-(1/2:ℝ))) := by
  obtain ⟨C,hC,hfinite⟩ := h.squarefreeModelMass_finite_error
  obtain ⟨E,hE,hEuler⟩ := radialEulerPartial_one_error
  obtain ⟨F,hF,hSieve⟩ := finiteSieveDensity_error
  obtain ⟨M,hM,hMellin⟩ := h.mellin_decay 1 0
  let P := |2*Real.pi/(9*Real.sqrt 3)| * M
  let K := C+P*(E+F)+1
  have hP : 0 ≤ P := mul_nonneg (abs_nonneg _) hM.le
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro i A D hA hD
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hDp : 0 < D := zero_lt_one.trans_le hD
  let B := Real.exp (h.realPower (-1/3)).radius
  let T := Real.sqrt (B*A)
  let ρ : ℂ := ((∑' a : Eisenstein,moebiusResidueTerm a):ℝ)
  let J : ℂ := ((A^(2/3:ℝ)*(2*Real.pi/(9*Real.sqrt 3)):ℝ):ℂ)*mellin (W i) (2/3)
  have hB : 1 ≤ B := Real.one_le_exp (h.realPower (-1/3)).radius_nonneg
  have hT : 0 < T := Real.sqrt_pos.mpr (mul_pos (zero_lt_one.trans_le hB) hAp)
  have hscale : T^(-(1/2:ℝ)) ≤ A^(-(1/4:ℝ)) := squarefree_density_scale hA hB
  have he : ‖metaplecticRadialEulerPartial 1 T-ρ‖ ≤ E*A^(-(1/4:ℝ)) :=
    (hEuler T hT).trans (mul_le_mul_of_nonneg_left hscale hE.le)
  have hs : ‖ρ-(finiteSieveDensity (squarefreeDivisorTruncation D):ℂ)‖ ≤
      F*D^(-(1/2:ℝ)) := by
    dsimp [ρ]
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
    exact hSieve D hD
  have hd : ‖metaplecticRadialEulerPartial 1 T-
      (finiteSieveDensity (squarefreeDivisorTruncation D):ℂ)‖ ≤
      E*A^(-(1/4:ℝ))+F*D^(-(1/2:ℝ)) := by
    calc
      _ = ‖(metaplecticRadialEulerPartial 1 T-ρ)+
          (ρ-(finiteSieveDensity (squarefreeDivisorTruncation D):ℂ))‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add he hs)
  have hm : ‖mellin (W i) (2/3)‖ ≤ M := by
    simpa using hMellin i (2/3) (by norm_num) 0
  have hJ : ‖J‖ ≤ P*A^(2/3:ℝ) := by
    dsimp [J,P]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hAp.le _)]
    calc
      _ ≤ A^(2/3:ℝ)*|2*Real.pi/(9*Real.sqrt 3)| * M :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by ring
  have ha : A^(1/6:ℝ) ≤ A^(5/12:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have hp : A^(2/3:ℝ)*A^(-(1/4:ℝ)) = A^(5/12:ℝ) := by
    rw [←Real.rpow_add hAp]
    norm_num
  calc
    _ = ‖(squarefreeModelMass (W i) A-J*metaplecticRadialEulerPartial 1 T)+
        J*(metaplecticRadialEulerPartial 1 T-
          (finiteSieveDensity (squarefreeDivisorTruncation D):ℂ))‖ := by dsimp [J]; congr 1; ring
    _ ≤ C*A^(1/6:ℝ)+‖J‖*‖metaplecticRadialEulerPartial 1 T-
        (finiteSieveDensity (squarefreeDivisorTruncation D):ℂ)‖ := by
      apply (norm_add_le _ _).trans
      rw [norm_mul]
      exact add_le_add (hfinite i A hAp) le_rfl
    _ ≤ C*A^(5/12:ℝ)+(P*A^(2/3:ℝ))*
        (E*A^(-(1/4:ℝ))+F*D^(-(1/2:ℝ))) := by
      exact add_le_add (mul_le_mul_of_nonneg_left ha hC.le)
        (mul_le_mul hJ hd (_root_.norm_nonneg _) (by positivity))
    _ = (C+P*E)*A^(5/12:ℝ)+P*F*(A^(2/3:ℝ)*D^(-(1/2:ℝ))) := by
      calc
        _ = C*A^(5/12:ℝ)+P*E*(A^(2/3:ℝ)*A^(-(1/4:ℝ)))+
            P*F*(A^(2/3:ℝ)*D^(-(1/2:ℝ))) := by ring
        _ = _ := by rw [hp]; ring
    _ ≤ K*(A^(5/12:ℝ)+A^(2/3:ℝ)*D^(-(1/2:ℝ))) := by
      rw [mul_add]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [K]
        nlinarith
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [K]
        nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeMassComparison
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact cube constant identifies the variance model with the
ordinary squarefree mass, with an explicit quantitative error. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma cubeModelTerm_density_identity (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (A ρ : ℝ) :
    (ρ:ℂ)*cubeModelTerm S β u V A =
      ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*
        (((A^(2/3:ℝ)*(2*Real.pi/(9*Real.sqrt 3)):ℝ):ℂ)*mellin V (2/3)*(ρ:ℂ)) := by
  rw [cubeModelTerm,cubeProfileIntegral_eq_mellin V hV hV']
  push_cast
  ring

theorem UniformLogWeights.cubeModelTerm_mass_error
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i (S : Finset Eisenstein) (β : Eisenstein → ℂ) (u A D : ℝ),
      1 ≤ A → 1 ≤ D →
      ‖(finiteSieveDensity (squarefreeDivisorTruncation D):ℂ)*cubeModelTerm S β u (W i) A-
        ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*squarefreeModelMass (W i) A‖ ≤
        K*‖dispersionModel S β u‖^2*(A^(5/12:ℝ)+A^(2/3:ℝ)*D^(-(1/2:ℝ))) := by
  obtain ⟨K,hK,hbound⟩ := h.squarefreeModelMass_density_error
  refine ⟨cStar^2*K,by have := cStar_pos; positivity,?_⟩
  intro i S β u A D hA hD
  rw [cubeModelTerm_density_identity S β u (W i) (h.compact i) (h.smooth i),
    ←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),norm_sub_rev]
  exact (mul_le_mul_of_nonneg_left (hbound i A D hA hD)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCubeMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite cube density equals the true squarefree model mass for
actual bounded stopped coefficients, with arbitrary logarithmic accuracy. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_cube_mass_log_saving {ξ κ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hκ : 0 < κ) (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦpos : tsupport Φ ⊆ Set.Ioi 0) (hΦ' : ContDiff ℝ ∞ Φ) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (W : ι → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein) (b u A : ℝ),
      X^κ ≤ b → b ≤ X → b^(3/2:ℝ) ≤ A →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected
      ‖(finiteSieveDensity (squarefreeDivisorTruncation ((Real.log X)^(2*k))):ℂ)*
          cubeModelTerm S β u Φ A-
        ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*squarefreeModelMass Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  let hv : UniformLogWeights (fun _ : Unit => Φ) := uniformLogWeights_constant Φ hΦ hΦpos hΦ'
  obtain ⟨C,hC,hmass⟩ := hv.cubeModelTerm_mass_error
  obtain ⟨E,hE,hmodel⟩ := stopped_model_norm (ι := ι) hξ hξz
  refine ⟨2*C*E^2,by positivity,?_⟩
  filter_upwards [hmodel,negative_power_log_saving (show 0 < κ*(3/8) by positivity) k,
    (tendsto_rpow_atTop hκ).eventually_ge_atTop 1,eventually_ge_atTop (Real.exp 1)]
    with X hmodel hdecay hlarge hX
  intro W hW selected e b u A hbX hbXhi hAlo
  dsimp only
  have hb1 : 1 ≤ b := hlarge.trans hbX
  have hbp : 0 < b := zero_lt_one.trans_le hb1
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hL1 : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hL1
  have hA1 : 1 ≤ A := (Real.one_le_rpow hb1 (by norm_num)).trans hAlo
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected
  have he : ‖dispersionModel S β u‖^2 ≤ E^2*b^(5/3:ℝ) := by
    have hm := pow_le_pow_left₀ (_root_.norm_nonneg _) (hmodel W hW selected e b 0 u hbp hbXhi) 2
    apply hm.trans_eq
    rw [mul_pow,←Real.rpow_mul_natCast hbp.le]
    norm_num
  have ha : A^(-(1/4:ℝ)) ≤ 1/(Real.log X)^k := by
    calc
      _ ≤ (b^(3/2:ℝ))^(-(1/4:ℝ)) := Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hbp _) hAlo (by norm_num)
      _ = b^(-(3/8:ℝ)) := by rw [←Real.rpow_mul hbp.le]; norm_num
      _ ≤ (X^κ)^(-(3/8:ℝ)) := Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hXp _) hbX (by norm_num)
      _ = X^(-(κ*(3/8))) := by rw [←Real.rpow_mul hXp.le]; congr 1; ring
      _ ≤ 1/(1+Real.log X)^k := hdecay
      _ ≤ _ := one_div_le_one_div_of_le (pow_pos hLp k)
        (pow_le_pow_left₀ hLp.le (by linarith) k)
  have hd : ((Real.log X)^(2*k))^(-(1/2:ℝ)) = 1/(Real.log X)^k := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hLp.le]
    have he : ((2*k:ℕ):ℝ)*(-(1/2:ℝ)) = -(k:ℝ) := by push_cast; ring
    rw [he,Real.rpow_neg hLp.le,Real.rpow_natCast,one_div]
  have hs : A^(5/12:ℝ)+A^(2/3:ℝ)*((Real.log X)^(2*k))^(-(1/2:ℝ)) ≤
      2*A^(2/3:ℝ)/(Real.log X)^k := by
    rw [hd,show A^(5/12:ℝ) = A^(2/3:ℝ)*A^(-(1/4:ℝ)) by
      rw [←Real.rpow_add hAp]; norm_num]
    exact (add_le_add (mul_le_mul_of_nonneg_left ha (by positivity)) le_rfl).trans_eq (by ring)
  have hb := hmass () S β u A ((Real.log X)^(2*k)) hA1 (one_le_pow₀ hL1)
  apply hb.trans
  calc
    _ ≤ C*(E^2*b^(5/3:ℝ))*(2*A^(2/3:ℝ)/(Real.log X)^k) :=
      mul_le_mul (mul_le_mul_of_nonneg_left he hC.le) hs (by positivity) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIMixedScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed product-support dilation is absorbed by the actual Type-I
margin. The corrected-square normalization is an exact power identity. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma typeIMixed_scale_identity {A L : ℝ} (hA : 0 < A) (hL : 0 < L) (η : ℝ) :
    A^(-1/6:ℝ)*L^(5/6:ℝ)*(L*A)^(5/6-η) =
      A^(2/3:ℝ)*L^(5/3:ℝ)*(L*A)^(-η) := by
  rw [Real.mul_rpow hL.le hA.le,Real.mul_rpow hL.le hA.le,
    show (5/6-η:ℝ) = (5/6)+(-η) by ring,
    Real.rpow_add hL,Real.rpow_add hA]
  have ha : A^(-1/6:ℝ)*A^(5/6:ℝ) = A^(2/3:ℝ) := by
    rw [←Real.rpow_add hA]
    norm_num
  have hl : L^(5/6:ℝ)*L^(5/6:ℝ) = L^(5/3:ℝ) := by
    rw [←Real.rpow_add hL]
    norm_num
  calc
    _ = (A^(-1/6:ℝ)*A^(5/6:ℝ))*(L^(5/6:ℝ)*L^(5/6:ℝ))*(L^(-η)*A^(-η)) := by ring
    _ = _ := by rw [ha,hl]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedMixedScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual early-stopped bilinear range automatically satisfies the
level condition of the published Type-I estimate. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_mixed_level {b A : ℝ} (hb : 2 ≤ b) (hA : b^(3/2:ℝ) ≤ A) :
    1 ≤ A ∧ 2 ≤ (b/2)*A ∧ b/2 ≤ ((b/2)*A)^(51/100:ℝ) := by
  have hb1 : 1 ≤ b := by linarith
  have hbp : 0 < b := by linarith
  have hbpower : b ≤ b^(3/2:ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hb1 (show (1:ℝ) ≤ 3/2 by norm_num)
  have hbA : b ≤ A := hbpower.trans hA
  have hr : 1 ≤ b/2 := by linarith
  have hrp : 0 < b/2 := zero_lt_one.trans_le hr
  have hprod : (b/2)^2 ≤ (b/2)*A := by nlinarith
  refine ⟨hb1.trans hbA,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hbA hrp.le
    nlinarith
  · calc
      _ ≤ (b/2)^((2:ℝ)*(51/100)) := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hr (show (1:ℝ) ≤ 2*(51/100) by norm_num)
      _ = ((b/2)^2)^(51/100:ℝ) := by rw [←Real.rpow_natCast (b/2) 2,←Real.rpow_mul hrp.le]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (sq_nonneg _) hprod (by norm_num)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeDivisorMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallBStoppedBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The height estimate applied to the literal stopped coefficients.
Both coefficient energies are derived; neither is a new input. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma outer_log_energy_conversion {A Z K : ℝ} (hA : 1 ≤ A) (hZ : 1 ≤ Z)
    (hAZ : A ≤ Z^2) (hK : 0 ≤ K) (d : ℕ) :
    K*(2*A)*(1+Real.log (2*A))^d ≤
      (2*K*(3+Real.log 2)^d)*A*(1+Real.log Z)^d := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hlA : Real.log A ≤ 2*Real.log Z := by
    have hh := Real.log_le_log hA0 hAZ
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hlZ := Real.log_nonneg hZ
  have hl2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hl : 1+Real.log (2*A) ≤ (3+Real.log 2)*(1+Real.log Z) := by
    rw [Real.log_mul (by norm_num) hA0.ne']
    nlinarith [mul_nonneg hl2 hlZ]
  have hp := pow_le_pow_left₀
    (show 0 ≤ 1+Real.log (2*A) by
      have hh := Real.log_nonneg (show 1 ≤ 2*A by linarith)
      linarith) hl d
  calc
    _ ≤ K*(2*A)*((3+Real.log 2)*(1+Real.log Z))^d :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by rw [mul_pow]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedOuterEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual stopped outer coefficient has logarithmic energy in the
same X-normalization as the stopped corrected-dispersion theorem. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem stopped_outer_log_energy (hpnt : PrimaryPrimePNT) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (E U P : Finset Eisenstein)
      (ψ : ℝ → ℝ) (w b A X : ℝ) (remaining : Eisenstein → Prop),
      (∀ e ∈ E, primary e) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      Real.exp 1 ≤ X → 2 ≤ b → b ≤ X → b^(3/2:ℝ) ≤ A → A ≤ b^2 →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ A ≤ norm a ∧ norm a ≤ 2*A) →
      (∑ a ∈ P, ‖stoppedAlpha E U ψ w remaining a‖^2) ≤
        K*A*(Real.log X)^d := by
  obtain ⟨K,d,hK,henergy⟩ := smallB_stopped_alpha_energy hpnt
  let M := 2*K*(3+Real.log 2)^d
  refine ⟨M*2^d,d,by dsimp [M]; positivity,?_⟩
  intro E U P ψ w b A X remaining hE hψ hX hb hbX hAlo hAhi hP
  have hb1 : 1 ≤ b := by linarith
  have hA1 : 1 ≤ A := (Real.one_le_rpow hb1 (by norm_num)).trans hAlo
  have hbpow : b ≤ b^(3/2:ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num : (1:ℝ) ≤ 3/2)
  have hA2 : 2 ≤ A := hb.trans (hbpow.trans hAlo)
  have hbig : Real.exp 1 ≤ 2*A := by linarith [Real.exp_one_lt_d9]
  have hL1 : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hLb : 1+Real.log b ≤ 2*Real.log X := by
    have hh := Real.log_le_log (by linarith : 0 < b) hbX
    linarith
  have he := henergy E U P ψ w (2*A) remaining hE hψ hbig
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.2⟩)
  apply (he.trans (outer_log_energy_conversion hA1 hb1 hAhi hK.le d)).trans
  change M*A*(1+Real.log b)^d ≤ (M*2^d)*A*(Real.log X)^d
  calc
    _ ≤ M*A*(2*Real.log X)^d := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith [Real.log_nonneg hb1]) hLb d)
      (by dsimp [M]; positivity)
    _ = _ := by rw [mul_pow]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedOverlapScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative overlap saving with the genuine active roughness threshold.
The outer energy and inner bounded coefficient have separate constants. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem bounded_active_model_overlap_log_saving (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) {A b z R M E : ℝ}
    (hA : 0 < A) (hb : 0 < b) (hz : 0 < z) (hR : 0 < R)
    (_hM : 0 ≤ M) (hE : 0 ≤ E) (k d : ℕ)
    (hP : ∀ a ∈ P, primary a ∧ A ≤ norm a ∧ norm a ≤ 2*A)
    (hB : ∀ a ∈ B, primary a ∧ Squarefree a ∧ b/2 ≤ norm a ∧ norm a ≤ b)
    (hα : (∑ a ∈ P, ‖α a‖^2) ≤ E*A*z^d)
    (hβ : ∀ a ∈ B, ‖β a‖ ≤ M)
    (hn : ∀ a ∈ B, β a ≠ 0 → ((primaryPrimeFactors a).card:ℝ) ≤ z/Real.log 2)
    (hrough : ∀ a ∈ B, β a ≠ 0 → ∀ p ∈ primaryPrimeFactors a, R ≤ norm p)
    (hthreshold : z^(d+1+2*k) ≤ R) :
    ‖modelOverlap P B α β u‖ ≤
      Real.sqrt (cStar^2*36*18*2*(36*M^2)*E/Real.log 2)*
        A^(5/6:ℝ)*b^(5/6:ℝ)/z^k := by
  let L := b/2
  have hL : 0 < L := by dsimp [L]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (B.card:ℝ) ≤ 36*L := by
    exact (primary_support_card_le B hb.le
      (fun a ha => ⟨(hB a ha).1,(hB a ha).2.2.2⟩)).trans_eq (by dsimp [L]; ring)
  have henergy : (∑ a ∈ B, ‖β a‖^2) ≤ (36*M^2)*L*z^0 := by
    calc
      _ ≤ ∑ _a ∈ B, M^2 := Finset.sum_le_sum (fun a ha =>
        pow_le_pow_left₀ (_root_.norm_nonneg _) (hβ a ha) 2)
      _ = (B.card:ℝ)*M^2 := by simp
      _ ≤ (36*L)*M^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg M)
      _ = _ := by simp only [pow_zero]; ring
  have hraw := active_modelOverlap_norm_sq_le P B α β u hA hL
    (show 0 ≤ 2*A by positivity) hR (show 0 ≤ z/Real.log 2 by positivity)
    (fun a ha => ⟨primary_ne_zero (hP a ha).1,(hP a ha).2⟩)
    (fun a ha => ⟨(hB a ha).1,(hB a ha).2.1,(hB a ha).2.2.1⟩) hn hrough
  let C := cStar^2*36*18*2*(36*M^2)*E/Real.log 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlog : z^(d+1)/R ≤ 1/z^(2*k) := by
    apply (div_le_div_of_nonneg_left (pow_nonneg hz.le _) (pow_pos hz _) hthreshold).trans_eq
    rw [pow_add z (d+1) (2*k)]
    field_simp
  have hsq : ‖modelOverlap P B α β u‖^2 ≤ C*A^(5/3:ℝ)*b^(5/3:ℝ)/z^(2*k) := by
    calc
      _ ≤ (cStar*A^(-1/6:ℝ)*L^(-1/6:ℝ))^2*
          ((36*L*(E*A*z^d))*((z/Real.log 2)*(18*(2*A)/R)*((36*M^2)*L*z^0))) := by
        apply hraw.trans
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul (mul_le_mul hcard hα (by positivity) (by positivity))
          (mul_le_mul_of_nonneg_left henergy (by positivity)) (by positivity) (by positivity)
      _ = C*A^(5/3:ℝ)*L^(5/3:ℝ)*(z^(d+1)/R) := by
        rw [model_overlap_scale hA hL]
        simp only [Nat.add_zero,pow_succ]
        dsimp [C]
        ring
      _ ≤ C*A^(5/3:ℝ)*L^(5/3:ℝ)*(1/z^(2*k)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ C*A^(5/3:ℝ)*b^(5/3:ℝ)*(1/z^(2*k)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow hL.le (by dsimp [L]; linarith) (by norm_num)
      _ = _ := by ring
  exact norm_le_bilinear_of_square hC hA hb hz k hsq

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSquarefreeModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete positive stopped variance has the true squarefree mass
as its model. Both the divisor sieve and the common-factor terms are actual
finite sums; no variance estimate is assumed. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_squarefree_model_log_saving
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦpos : tsupport Φ ⊆ Set.Ioi 0) (hΦ' : ContDiff ℝ ∞ Φ) (k H : ℕ) :
    ∃ (K : ℝ) (G : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(3*(k+2*(2*k))) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      let T := squarefreeDivisorTruncation ((Real.log X)^(2*k))
      ‖sievedDispersionVariance T S β u Φ A-
        ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*squarefreeModelMass Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  obtain ⟨K,G,hK,hvariance⟩ := stopped_sieved_model_log_saving (ι := ι) (E := E)
    hpnt hSW hMV hC hHuxley hξ hξz hκ hF hJ Φ hΦ hΦ' k H (2*k)
  obtain ⟨D,hD,hmass⟩ := stopped_cube_mass_log_saving (ι := ι) hξ hξz hκ Φ hΦ hΦpos hΦ' k
  refine ⟨K+D,G,by positivity,?_⟩
  filter_upwards [hvariance,hmass] with X hvariance hmass
  intro δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF W hW hWi hWd
    hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hR
  dsimp only
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let T := squarefreeDivisorTruncation ((Real.log X)^(2*k))
  have hv := hvariance δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF
    W hW hWi hWd hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hR
  have hm := hmass W hW
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early) e b u A hbXlo hbXhi hAlo
  change ‖sievedDispersionVariance T S β u Φ A-
    ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*squarefreeModelMass Φ A‖ ≤ _
  calc
    _ ≤ ‖sievedDispersionVariance T S β u Φ A-(finiteSieveDensity T:ℂ)*cubeModelTerm S β u Φ A‖+
        ‖(finiteSieveDensity T:ℂ)*cubeModelTerm S β u Φ A-
          ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*squarefreeModelMass Φ A‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := (add_le_add hv hm).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIMixedFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite, literal versions of the Type-I mixed term and its squarefree
product model. These identities do not remove common prime divisors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma typeIMixedGauss_finite (r : Eisenstein) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) :
    typeIMixedGauss r W U = ∑ u ∈ primaryElementBall F,
      W (norm u/U)*((norm u^(-1/6:ℝ):ℝ):ℂ)*gauss (u*r) := by
  let S := (primaryElementBall F).subtype primary
  have he : typeIMixedGauss r W U = ∑ u ∈ S,
      gauss (r*u)*((norm u^(-1/6:ℝ):ℝ):ℂ)*W (norm u/U) := by
    apply tsum_eq_sum
    intro u hu
    have hnorm : F < norm u := by
      by_contra hn
      exact hu (Finset.mem_subtype.mpr (mem_primaryElementBall.mpr ⟨u.property,le_of_not_gt hn⟩))
    rw [hW _ ((lt_div_iff₀ hU).mpr (hBF.trans_lt hnorm)),mul_zero]
  rw [he]
  dsimp only [S]
  rw [Finset.sum_subtype_of_mem
    (fun u : Eisenstein => gauss (r*u)*((norm u^(-1/6:ℝ):ℝ):ℂ)*W (norm u/U))
    (fun _ hu => (mem_primaryElementBall.mp hu).1)]
  apply Finset.sum_congr rfl
  intro u _
  rw [mul_comm u r]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MixedTermIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Connect the literal Type-I sums to the exact mixed term and its
coprimality model; this is purely finite algebra and power normalization. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma typeIMixedModel_eq_mass (r : Eisenstein) (W : ℝ → ℂ) (A : ℝ) :
    typeIMixedModel r W A =
      ((cStar*norm r^(-1/6:ℝ):ℝ):ℂ)*coprimeSquarefreeModelMass r W A := by
  rw [typeIMixedModel,coprimeSquarefreeModelMass,←tsum_mul_left]
  apply tsum_congr
  intro a
  by_cases ha : primary a
  · simp only [ha,ite_true, if_true]
    have hn : 0 < norm a := norm_pos_of_ne_zero (primary_ne_zero ha)
    have hp : norm (r*a)^(-1/6:ℝ)*norm a^(-1/6:ℝ) =
        norm r^(-1/6:ℝ)*norm a^(-1/3:ℝ) := by
      rw [norm_mul_eq,Real.mul_rpow (norm_nonneg r) hn.le,mul_assoc,←Real.rpow_add hn]
      norm_num
    calc
      _ = (idealMoebius (r*a):ℂ)^2*
          ((cStar*(norm (r*a)^(-1/6:ℝ)*norm a^(-1/6:ℝ)):ℝ):ℂ)*W (norm a/A) := by push_cast; ring
      _ = _ := by rw [hp]; push_cast; ring
  · simp only [ha,ite_false, if_false,mul_zero]

lemma typeIMixedModel_sum_eq (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    (∑ b ∈ S, β b*normTwist u b*typeIMixedModel b W A) = mixedMassModel S β u W A := by
  unfold mixedMassModel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [typeIMixedModel_eq_mass]
  push_cast
  ring

lemma typeIMixedGauss_sum_eq (S : Finset Eisenstein) (hS : ∀ b ∈ S, primary b)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) {A R F : ℝ}
    (hA : 0 < A) (hRF : R*A ≤ F) (hcut : ∀ x, R < x → W x = 0) :
    (∑ b ∈ S, β b*normTwist u b*typeIMixedGauss b W A) =
      ∑ a ∈ primaryElementBall F, (idealMoebius a:ℂ)^2*W (norm a/A)*gauss a*
        ((norm a^(-1/6:ℝ):ℝ):ℂ)*dispersionPolynomial S β u a := by
  calc
    _ = ∑ b ∈ S, β b*normTwist u b*(∑ a ∈ primaryElementBall F,
        (W (norm a/A)*((norm a^(-1/6:ℝ):ℝ):ℂ))*gauss (a*b)) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [typeIMixedGauss_finite b W hA hRF hcut]
    _ = ∑ a ∈ primaryElementBall F, (idealMoebius a:ℂ)^2*
        (W (norm a/A)*((norm a^(-1/6:ℝ):ℝ):ℂ))*gauss a*dispersionPolynomial S β u a :=
      (dispersion_mixed_finite _ _ (fun a ha => (mem_primaryElementBall.mp ha).1)
        hS _ β u).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CorrectedSquareTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the proved complex variance and Type-I estimates to the
actual nonnegative corrected square. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem correctedSquareMass_le_of_errors (C S : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c) (h1 : 1 ∈ C) (hS : ∀ b ∈ S, primary b)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    {A R : ℝ} (hA : 0 < A) (hcut : ∀ x, R < x → V x = 0)
    (E₁ E₂ : ℝ)
    (hvariance : ‖sievedDispersionVariance C S β u (fun x => (V x:ℂ)) A-
      ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*
        squarefreeModelMass (fun x => (V x:ℂ)) A‖ ≤ E₁)
    (hmixed : ‖((cStar:ℂ)*star (dispersionModel S β u))*
      (∑ b ∈ S, β b*normTwist u b*typeIMixedGauss b (fun x => (V x:ℂ)) A)-
      ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*
        squarefreeModelMass (fun x => (V x:ℂ)) A‖ ≤ E₂) :
    correctedSquareMass S β u V A ≤ E₁+2*E₂ := by
  have hmodel : ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*
      squarefreeModelMass (fun x => (V x:ℂ)) A =
      (((cStar^2*‖dispersionModel S β u‖^2)*
        (∑ a ∈ primaryElementBall (R*A), (idealMoebius a:ℝ)^2*V (norm a/A)*
          norm a^(-1/3:ℝ)):ℝ):ℂ) := by
    rw [squarefreeModelMass_ofReal V hA le_rfl hcut]
    push_cast
    rfl
  have hp := hvariance
  rw [sievedDispersionVariance_ofReal C S β u V hA le_rfl hcut,hmodel,
    ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hp
  have hm := hmixed
  rw [typeIMixedGauss_sum_eq S hS β u (fun x => (V x:ℂ)) hA le_rfl
    (fun x hx => by rw [hcut x hx]; rfl),hmodel] at hm
  rw [correctedSquareMass_eq_sum S β u V hA le_rfl hcut]
  exact corrected_dispersion_finite_error _ C S
    (fun a ha => (mem_primaryElementBall.mp ha).1) hC h1
    (fun a => V (norm a/A)) (fun a _ => hV _) β u E₁ E₂ hp hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CorrectedDispersionTheorem
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete corrected dispersion estimate. The positive variance,
Type-I mixed term and squarefree model are actual arithmetic sums. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma correction_factor_model (s m : ℂ) :
    ((cStar:ℂ)*star s)*((cStar:ℂ)*s*m) =
      ((cStar^2*‖s‖^2:ℝ):ℂ)*m := by
  calc
    _ = (cStar:ℂ)^2*(star s*s)*m := by ring
    _ = _ := by
      have hs := Complex.conj_mul' s
      simp only [starRingEnd_apply] at hs
      rw [hs]
      push_cast
      rfl

lemma correction_mixed_error (s z q m : ℂ) (E₁ E₂ : ℝ)
    (h₁ : ‖((cStar:ℂ)*star s)*(z-q)‖ ≤ E₁)
    (h₂ : ‖((cStar:ℂ)*star s)*(q-(cStar:ℂ)*s*m)‖ ≤ E₂) :
    ‖((cStar:ℂ)*star s)*z-((cStar^2*‖s‖^2:ℝ):ℂ)*m‖ ≤ E₁+E₂ := by
  calc
    _ = ‖((cStar:ℂ)*star s)*(z-q)+
        ((cStar:ℂ)*star s)*(q-(cStar:ℂ)*s*m)‖ := by
      congr 1
      rw [mul_sub,mul_sub,correction_factor_model]
      ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add h₁ h₂)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralStoppedMixedLogSaving
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The corrected mixed-term error for the actual stopped coefficient.
The product-squarefree model is retained; the remaining model-coprimality
comparison belongs to the variance assembly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem stopped_corrected_mixed_log_saving_actual
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVp : tsupport V ⊆ Set.Ioi 0)
    (hVs : ContDiff ℝ ∞ V)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {ξ κ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein) (b A u : ℝ),
      X^κ ≤ b → b ≤ X → b^(3/2:ℝ) ≤ A →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected
      ‖((cStar:ℂ)*star (dispersionModel S β u))*
        ((∑ r ∈ S, β r*normTwist u r*typeIMixedGauss r V A)-mixedMassModel S β u V A)‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  let hw : UniformLogWeights (fun _ : Unit => V) := uniformLogWeights_constant V hVc hVp hVs
  let B := Real.exp hw.radius
  have hB : 1 ≤ B := Real.one_le_exp hw.radius_nonneg
  obtain ⟨K,hK,htype⟩ := stopped_typeI_mixed_actual (ι := ι)  hw hGamma hB hξ hξz
  obtain ⟨D,hD,hmodel⟩ := stopped_model_norm (ι := ι) hξ hξz
  have hcStar : 0 < cStar := cStar_pos
  let E := cStar*D*K
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨E+1,by positivity,?_⟩
  filter_upwards [htype,hmodel,
    (tendsto_rpow_atTop hκ).eventually_ge_atTop (max 2 (2*B)),
    negative_power_log_saving (show 0 < κ/100 by positivity) k,
    eventually_ge_atTop (Real.exp 1)] with X htype hmodel hlarge hdecay hX
  intro W hW selected e b A u hb hbX hAlo
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected
  have hb2 : 2 ≤ b := ((le_max_left _ _).trans hlarge).trans hb
  have hBb : 2*B ≤ b := ((le_max_right _ _).trans hlarge).trans hb
  have hbp : 0 < b := by linarith
  obtain ⟨hA1,hprod,hlevel⟩ := stopped_mixed_level hb2 hAlo
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  have hBA : B ≤ (b/2)*A := by
    have hh := le_mul_of_one_le_right (show 0 ≤ b/2 by positivity) hA1
    linarith
  have hcut (r : Eisenstein) (_hr : r ∈ S) (x : ℝ) (hx : B < x) : V x = 0 := by
    by_contra hn
    exact (not_le_of_gt hx) (hw.annular_support () (subset_tsupport V hn)).2
  have ht := htype W hW selected e (fun _ => ()) b A u hb2 hbX hA1 hprod hBA hlevel hcut
  have hphase (r : Eisenstein) : stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected r =
      β r*normTwist u r := by
    rw [stoppedRowCoefficient_phase,normTwist_eq_mellinPhase]
  have heq : (∑ r ∈ S, stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected r*
      (typeIMixedGauss r V A-typeIMixedModel r V A)) =
      (∑ r ∈ S, β r*normTwist u r*typeIMixedGauss r V A)-mixedMassModel S β u V A := by
    simp_rw [hphase,mul_sub]
    rw [Finset.sum_sub_distrib,typeIMixedModel_sum_eq]
  change ‖∑ r ∈ S, stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected r*
    (typeIMixedGauss r V A-typeIMixedModel r V A)‖ ≤ _ at ht
  rw [heq] at ht
  have ht' : ‖(∑ r ∈ S, β r*normTwist u r*typeIMixedGauss r V A)-mixedMassModel S β u V A‖ ≤
      K*A^(-1/6:ℝ)*(b*A)^(5/6-1/100:ℝ) := ht.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (by nlinarith) (by norm_num)) (by positivity))
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hz : 0 < Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) hX
    rw [Real.log_exp] at hh
    linarith
  have hsmall : (b*A)^(-(1/100):ℝ) ≤ 1/(Real.log X)^k := by
    have hba : b ≤ b*A := le_mul_of_one_le_right hbp.le hA1
    have h₁ := Real.rpow_le_rpow_of_nonpos hbp hba (by norm_num : -(1/100:ℝ) ≤ 0)
    have h₂ := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hXp κ) hb
      (by norm_num : -(1/100:ℝ) ≤ 0)
    rw [←Real.rpow_mul hXp.le] at h₂
    have he : κ*(-(1/100:ℝ)) = -(κ/100) := by ring
    rw [he] at h₂
    exact ((h₁.trans h₂).trans hdecay).trans
      (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hz.le (by linarith) k))
  change ‖((cStar:ℂ)*star (dispersionModel S β u))*_‖ ≤ _
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos cStar_pos,norm_star]
  calc
    _ ≤ (cStar*(D*b^(5/6:ℝ)))*(K*A^(-1/6:ℝ)*(b*A)^(5/6-1/100:ℝ)) := by
      apply mul_le_mul _ ht' (_root_.norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (hmodel W hW selected e b 0 u hbp hbX) cStar_pos.le
    _ = E*(A^(2/3:ℝ)*b^(5/3:ℝ))*(b*A)^(-(1/100):ℝ) := by
      calc
        _ = E*(A^(-1/6:ℝ)*b^(5/6:ℝ)*(b*A)^(5/6-1/100:ℝ)) := by dsimp [E]; ring
        _ = _ := by rw [typeIMixed_scale_identity hAp hbp (1/100)]; ring
    _ ≤ E*(A^(2/3:ℝ)*b^(5/3:ℝ))*(1/(Real.log X)^k) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = E*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : E ≤ E+1)
          (Real.rpow_nonneg hAp.le _)) (Real.rpow_nonneg hbp.le _))
      (pow_nonneg hz.le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralStoppedCorrectedDispersion
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corrected dispersion for the actual early-stopped coefficients. The
positive variance, its common-factor restoration, the squarefree mass,
and the product-squarefree mixed term are all derived arithmetic sums. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem stopped_corrected_dispersion_log_saving_actual
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
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
    {RΦ : ℝ} (hcut : ∀ x, RΦ < x → Φ x = 0) (k H : ℕ) :
    ∃ (K : ℝ) (G : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(3*(k+2*(2*k))) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      correctedSquareMass S β u Φ A ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  let Ψ := fun x => (Φ x:ℂ)
  obtain ⟨Kp,G₀,hKp,hpositive⟩ := stopped_squarefree_model_log_saving (ι := ι) (E := E)
    hpnt hSW hMV hC hHuxley hξ hξz hκ hF hJ Ψ hΦ hΦpos hΦ' k H
  obtain ⟨Kt,hKt,htype⟩ := stopped_corrected_mixed_log_saving_actual (ι := ι)
     Ψ hΦ hΦpos hΦ' hGamma hξ hξz hκ k
  obtain ⟨Km,hKm,hmodel⟩ := stopped_mixed_model_log_saving (ι := ι)
    hξ hξz hκ Ψ hΦ hΦpos hΦ' k
  let G := max G₀ (k+1)
  refine ⟨Kp+2*(Kt+Km),G,by positivity,?_⟩
  filter_upwards [hpositive,htype,hmodel,eventually_ge_atTop (Real.exp 1)]
    with X hpositive htype hmodel hX
  intro δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF W hW hWi hWd
    hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hR
  dsimp only
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let T := squarefreeDivisorTruncation ((Real.log X)^(2*k))
  have hL1 : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hAp : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < b) _).trans_le hAlo
  have hR₀ : 2*(Real.log X)^G₀ ≤ min (X^ξ) (geometricBinLower (1+δ) X h) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (le_max_left _ _)) (by norm_num)).trans hR
  have hR₁ : (Real.log X)^(k+1) ≤ min (X^ξ) (geometricBinLower (1+δ) X h) := by
    have hp := pow_le_pow_right₀ hL1 (le_max_right G₀ (k+1))
    have hn : 0 ≤ (Real.log X)^G := by positivity
    change 2*(Real.log X)^G ≤ _ at hR
    change (Real.log X)^(k+1) ≤ (Real.log X)^G at hp
    linarith
  have hp := hpositive δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF
    W hW hWi hWd hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hR₀
  have ht := htype W hW
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early) e b A u hbXlo hbXhi hAlo
  have hm := hmodel δ b A u hδ hδone hbXlo hbXhi hAp W hW e
    j₀ k₀ h Z Q early hj hR₁
  have hmix := correction_mixed_error (dispersionModel S β u)
    (∑ r ∈ S, β r*normTwist u r*typeIMixedGauss r Ψ A)
    (mixedMassModel S β u Ψ A) (squarefreeModelMass Ψ A) _ _ ht hm
  have hT : ∀ d ∈ T, primary d := fun d hd => (mem_squarefreeDivisorTruncation.mp hd).1
  have hT1 : 1 ∈ T := mem_squarefreeDivisorTruncation.mpr
    ⟨primary_one,squarefree_one,by simpa only [norm_one_eq] using (one_le_pow₀ hL1)⟩
  have hS : ∀ r ∈ S, primary r := fun r hr => (stoppedIntervalSupport_spec X (b/2) b e hr).1
  apply (correctedSquareMass_le_of_errors T S hT hT1 hS β u Φ hΦnn hAp hcut _ _ hp hmix).trans_eq
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralStoppedCenteredBilinear
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual stopped coefficients satisfy the centered bilinear estimate.
Both energies and the shared-prime correction are derived from their
finite formulas; the early-label roughness condition remains explicit. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem stopped_centered_bilinear_log_saving_actual_oai
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
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
    {RΦ : ℝ} (hcut : ∀ x, RΦ < x → Φ x = 0) (k H : ℕ) :
    ∃ (d G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(15*(2*k+d)) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      ∀ (E₀ U P : Finset Eisenstein) (ψ : ℝ → ℝ) (w : ℝ)
        (remaining : Eisenstein → Prop),
      (∀ c ∈ E₀, primary c) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      (∀ c ∈ P, primary c ∧ Squarefree c ∧ A ≤ norm c ∧ norm c ≤ 2*A) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      ‖∑ c ∈ P, ∑ r ∈ S, stoppedAlpha E₀ U ψ w remaining c*β r*
        centeredGauss (c*r)*normTwist u (c*r)‖ ≤
        K*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k := by
  obtain ⟨Ka,d,hKa,halpha⟩ := stopped_outer_log_energy hpnt
  obtain ⟨Kp,G₀,hKp,hpositive⟩ := stopped_corrected_dispersion_log_saving_actual (ι := ι) (E := E)
    hpnt hSW hMV hC hHuxley  hGamma hξ hξz hκ hF hJ
    Φ hΦnn hΦ hΦpos hΦ' hcut (2*k+d) H
  obtain ⟨M,hM,hcoeff⟩ := stopped_interval_energy (ι := ι) hξ hξz
  let G := max G₀ (d+1+2*k)
  let D := cStar^2*36*18*2*(36*M^2)*Ka/Real.log 2
  refine ⟨d,G,Real.sqrt (Ka*Kp)+Real.sqrt D+1,by positivity,?_⟩
  filter_upwards [hpositive,hcoeff,eventually_ge_atTop (Real.exp 1)]
    with X hpositive hcoeff hX
  intro δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF W hW hWi hWd
    hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hR E₀ U P ψ w remaining hE₀ hψ hP
  dsimp only
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let α := stoppedAlpha E₀ U ψ w remaining
  let R := min (X^ξ) (geometricBinLower (1+δ) X h)
  have hbp : 0 < b := by linarith
  have hAp : 0 < A := (Real.rpow_pos_of_pos hbp _).trans_le hAlo
  have hL1 : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hL1
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hAhi' : A ≤ b^2/(Real.log X)^(3*((2*k+d)+2*(2*(2*k+d)))) := by
    simpa only [show 3*((2*k+d)+2*(2*(2*k+d)))=15*(2*k+d) by omega] using hAhi
  have hAupper : A ≤ b^2 := hAhi.trans
    (div_le_self (sq_nonneg _) (one_le_pow₀ hL1))
  have hR₀ : 2*(Real.log X)^G₀ ≤ R :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (le_max_left _ _)) (by norm_num)).trans hR
  have hR₁ : (Real.log X)^(d+1+2*k) ≤ R := by
    have hh := pow_le_pow_right₀ hL1 (le_max_right G₀ (d+1+2*k))
    change (Real.log X)^(d+1+2*k) ≤ (Real.log X)^G at hh
    change 2*(Real.log X)^G ≤ R at hR
    linarith [pow_nonneg hLp.le G]
  have hRp : 0 < R := (pow_pos hLp _).trans_le hR₁
  have hα : (∑ c ∈ P, ‖α c‖^2) ≤ Ka*A*(Real.log X)^d :=
    halpha E₀ U P ψ w b A X remaining hE₀ hψ hX hb hbXhi hAlo hAupper hP
  have hβ : ∀ r ∈ S, ‖β r‖ ≤ M := (hcoeff W hW _ 0 (b/2) b e hbp.le hbXhi).1
  have hS (r : Eisenstein) (hr : r ∈ S) :
      primary r ∧ Squarefree r ∧ b/2 ≤ norm r ∧ norm r ≤ b := by
    have hh := stoppedIntervalSupport_spec X (b/2) b e hr
    exact ⟨hh.1,hh.2.1,(Finset.mem_filter.mp hr).2.2.2.1.le,hh.2.2⟩
  have hn (r : Eisenstein) (hr : r ∈ S) (_hz : β r ≠ 0) :
      ((primaryPrimeFactors r).card:ℝ) ≤ Real.log X/Real.log 2 :=
    (primary_prime_factors_card_log (hS r hr).1).trans
      (div_le_div_of_nonneg_right (Real.log_le_log
        (norm_pos_of_ne_zero (primary_ne_zero (hS r hr).1))
        ((hS r hr).2.2.2.trans hbXhi)) (Real.log_pos (by norm_num)).le)
  have hrough (r : Eisenstein) (hr : r ∈ S) (hz : β r ≠ 0)
      (p : Eisenstein) (hp : p ∈ primaryPrimeFactors r) : R ≤ norm p :=
    stoppedRowCoefficient_early_roughness X (X^ξ) (X^(2/5:ℝ)) 0 (1+δ) Z Q W
      (Real.rpow_pos_of_pos hXp _) (Real.rpow_le_rpow_of_exponent_le hX1 hξz)
      (by linarith) (by linarith) j₀ k₀ h early hj hz
      (primaryPrimeFactor_spec (hS r hr).1 hp).1 (primaryPrimeFactor_spec (hS r hr).1 hp).2
  have hp := hpositive δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF
    W hW hWi hWd hAlo hAhi' e he hNe j₀ k₀ h Z Q early hj hR₀
  have hcorr := corrected_bilinear_log_saving P S α β u
    (fun c hc => (hP c hc).1) (fun r hr => (hS r hr).1) Φ hΦnn
    hAp hbp hLp hKa.le hKp.le hcut
    (fun c hc => hΦone _ ⟨(le_div_iff₀ hAp).mpr (by simpa using (hP c hc).2.2.1),
      (div_le_iff₀ hAp).mpr (by simpa [mul_comm] using (hP c hc).2.2.2)⟩) k d hα hp
  have hover := bounded_active_model_overlap_log_saving P S α β u hAp hbp hLp hRp hM.le hKa.le
    k d (fun c hc => ⟨(hP c hc).1,(hP c hc).2.2⟩) hS hα hβ hn hrough hR₁
  change ‖∑ c ∈ P, ∑ r ∈ S, α c*β r*centeredGauss (c*r)*normTwist u (c*r)‖ ≤ _
  rw [centered_bilinear_eq_correction_add_overlap P S α β u
    (fun c hc => (hP c hc).1) (fun r hr => ⟨(hS r hr).1,(hS r hr).2.1⟩)]
  apply (norm_add_le _ _).trans ((add_le_add hcorr hover).trans ?_)
  change Real.sqrt (Ka*Kp)*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k+
    Real.sqrt D*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k ≤ _
  calc
    _ = (Real.sqrt (Ka*Kp)+Real.sqrt D)*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith :
          Real.sqrt (Ka*Kp)+Real.sqrt D ≤ Real.sqrt (Ka*Kp)+Real.sqrt D+1)
          (Real.rpow_nonneg hAp.le _)) (Real.rpow_nonneg hbp.le _))
      (pow_nonneg hLp.le _)

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.stopped_centered_bilinear_log_saving_actual_oai.{u_1} := @OAI.CubicFirstMoment.stopped_centered_bilinear_log_saving_actual_oai.{u_1}
