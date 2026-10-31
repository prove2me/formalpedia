-- Prove2me | solution 1 for OAI.CubicFirstMoment.angular_balanced_common_squarefree_exponents
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:02:37.774276+00:00
-- url     : https://prove2.me/submissions/03250cfa-b2bd-4519-88c2-238d77c60dd0

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_angular_balanced_smooth_product_neighborhood

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_SieveMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma idealExponentNorm_mono {ν κ : EisensteinIdealExponent} (h : ν ≤ κ) :
    idealExponentNorm ν ≤ idealExponentNorm κ := by
  rw [← add_tsub_cancel_of_le h, idealExponentNorm_add]
  exact le_mul_of_one_le_right (idealExponentNorm_pos ν).le (idealExponentNorm_ge_one _)

/-- On the powers of one prime ideal, Dirichlet convolution with the
constant-one function is the ordinary partial sum of coefficients. -/
lemma coeff_mul_zeta_single (A : EisensteinArithmeticFunction)
    (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p n) (A * idealZeta) =
      ∑ k ∈ Finset.range (n + 1), MvPowerSeries.coeff (Finsupp.single p k) A := by
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk,
    MvPowerSeries.coeff_apply, idealZeta, mul_one]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k _ => A (Finsupp.single p k)) n

lemma coeff_single_eq_zeta_difference (A : EisensteinArithmeticFunction)
    (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p (n + 1)) A =
      MvPowerSeries.coeff (Finsupp.single p (n + 1)) (A * idealZeta) -
        MvPowerSeries.coeff (Finsupp.single p n) (A * idealZeta) := by
  rw [coeff_mul_zeta_single, coeff_mul_zeta_single, Finset.sum_range_succ]
  ring

lemma idealZeta_mul_moebiusSeries : idealZeta * idealMoebiusSeries = 1 := by
  rw [mul_comm, idealMoebiusSeries_mul_zeta]

private lemma exponent_fst_le {ν : EisensteinIdealExponent}
    {p : EisensteinIdealExponent × EisensteinIdealExponent}
    (hp : p ∈ Finset.HasAntidiagonal.antidiagonal ν) :
    p.1 ≤ ν := by
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← h]
  exact le_add_of_nonneg_right zero_le

/-- The truncated Möbius inverse agrees with the full inverse on every
divisor of an ideal whose norm is at most the truncation threshold. -/
lemma shortMoebiusResidual_low_norm (F : ℝ) (ν : EisensteinIdealExponent)
    (hν : idealExponentNorm ν ≤ Real.sqrt F) :
    MvPowerSeries.coeff ν (shortMoebiusResidual F) = 0 := by
  have he : MvPowerSeries.coeff ν (shortIdealMoebius F * idealZeta) =
      MvPowerSeries.coeff ν (idealMoebiusSeries * idealZeta) := by
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hn := (idealExponentNorm_mono (exponent_fst_le hp)).trans hν
    simp only [MvPowerSeries.coeff_apply, shortIdealMoebius, ite_eq_left hn]
  change MvPowerSeries.coeff ν (1 - shortIdealMoebius F * idealZeta) = 0
  rw [map_sub, he, idealMoebiusSeries_mul_zeta, sub_self]

/-- Both nonzero factors of the residual must have norm greater than
`sqrt F`; hence its square vanishes throughout the actual norm ball `F`. -/
lemma shortMoebiusResidual_sq_low_norm {F : ℝ} (hF : 0 ≤ F)
    (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν ((shortMoebiusResidual F) ^ 2) = 0 := by
  rw [pow_two, MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hfst : idealExponentNorm p.1 ≤ Real.sqrt F
  · rw [shortMoebiusResidual_low_norm F p.1 hfst, zero_mul]
  · have hsnd : idealExponentNorm p.2 ≤ Real.sqrt F := by
      have hprod : idealExponentNorm p.1 * idealExponentNorm p.2 ≤ F := by
        rw [← idealExponentNorm_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
        exact hν
      have hroot := Real.sqrt_nonneg F
      have hsq := Real.sq_sqrt hF
      by_contra h
      have ha := lt_of_not_ge hfst
      have hb := lt_of_not_ge h
      nlinarith
    rw [shortMoebiusResidual_low_norm F p.2 hsnd, mul_zero]

lemma shortMoebiusResidual_sq_mul_low_norm {F : ℝ} (hF : 0 ≤ F)
    (L : EisensteinArithmeticFunction) (ν : EisensteinIdealExponent)
    (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν ((shortMoebiusResidual F) ^ 2 * L) = 0 := by
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [shortMoebiusResidual_sq_low_norm hF p.1
    ((idealExponentNorm_mono (exponent_fst_le hp)).trans hν), zero_mul]

lemma idealZeta_mul_vonMangoldt : idealZeta * idealVonMangoldt = idealLogNorm := by
  rw [idealVonMangoldt, ← mul_assoc, idealZeta_mul_moebiusSeries, one_mul]

/-- The ideal von Mangoldt weight on every positive prime power is
exactly the logarithm of the prime-ideal norm. -/
lemma idealVonMangoldt_prime_power (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p (n + 1)) idealVonMangoldt =
      Real.log (normNat (idealPrimeRepresentative p)) := by
  rw [coeff_single_eq_zeta_difference, mul_comm idealVonMangoldt idealZeta,
    idealZeta_mul_vonMangoldt]
  simp only [MvPowerSeries.coeff_apply, idealLogNorm, idealExponentNorm_single,
    Real.log_pow]
  push_cast
  ring

/-- The short Möbius convolution identity throughout the sharp norm ball. -/
theorem short_moebius_identity {F : ℝ} (hF : 0 ≤ F)
    (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      MvPowerSeries.coeff ν
        ((2 * shortIdealMoebius F - shortIdealMoebius F * shortIdealMoebius F * idealZeta) *
          idealLogNorm) := by
  have halg : idealVonMangoldt -
      (2 * shortIdealMoebius F - shortIdealMoebius F * shortIdealMoebius F * idealZeta) *
        (idealZeta * idealVonMangoldt) = (shortMoebiusResidual F) ^ 2 * idealVonMangoldt := by
    unfold shortMoebiusResidual
    ring
  have h := congrArg (MvPowerSeries.coeff ν) halg
  rw [map_sub, idealZeta_mul_vonMangoldt,
    shortMoebiusResidual_sq_mul_low_norm hF idealVonMangoldt ν hν] at h
  exact sub_eq_zero.mp h

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

lemma shortIdealMoebius_abs_le_one (F : ℝ) (ν : EisensteinIdealExponent) :
    |MvPowerSeries.coeff ν (shortIdealMoebius F)| ≤ 1 := by
  change |if idealExponentNorm ν ≤ Real.sqrt F then _ else (0 : ℝ)| ≤ 1
  split_ifs
  · exact idealMoebiusSeries_abs_le_one ν
  · norm_num

lemma idealExponentOf_support_card {a : Eisenstein} (ha : Squarefree a) :
    (idealExponentOf a).support.card = (UniqueFactorizationMonoid.factors a).card := by
  have hnodup : (Associates.factors' a).Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    exact (idealExponentOf_squarefree_iff ha.ne_zero).mpr ha
  change (Associates.factors' a).toFinset.card = _
  rw [Multiset.toFinset_card_of_nodup hnodup]
  have h := congrArg Multiset.card (Associates.map_subtype_coe_factors' (a := a))
  simpa only [Multiset.card_map] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealVonMangoldt
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The convolution definition of ideal von Mangoldt has exactly its usual
prime-power coefficients. This is the arithmetic bridge for prime replacement
in the short Möbius decomposition. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealLogNorm_prime_difference (ν : EisensteinIdealExponent)
    (p : EisensteinIdealPrime) (hp : 1 ≤ ν p) :
    MvPowerSeries.coeff ν idealLogNorm -
        MvPowerSeries.coeff (ν - Finsupp.single p 1) idealLogNorm =
      Real.log (normNat (idealPrimeRepresentative p)) := by
  have hle : Finsupp.single p 1 ≤ ν := Finsupp.single_le_iff.mpr hp
  have he : ν = (ν - Finsupp.single p 1) + Finsupp.single p 1 :=
    (tsub_add_cancel_of_le hle).symm
  change Real.log (idealExponentNorm ν) -
    Real.log (idealExponentNorm (ν - Finsupp.single p 1)) = _
  conv_lhs => lhs; rw [he, idealExponentNorm_add]
  rw [Real.log_mul (idealExponentNorm_pos _).ne' (idealExponentNorm_pos _).ne',
    idealExponentNorm_single, pow_one]
  ring

private lemma coeff_logNorm_finite_nonempty (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) (hS : S.Nonempty) (hν : S ⊆ ν.support) :
    MvPowerSeries.coeff ν (idealLogNorm * finiteIdealMoebius S) =
      if S.card = 1 then ∑ p ∈ S, Real.log (normNat (idealPrimeRepresentative p)) else 0 := by
  induction S using Finset.induction_on generalizing ν with
  | empty => exact (Finset.not_nonempty_empty hS).elim
  | @insert p S hp ih =>
    have hνp : 1 ≤ ν p := Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp (hν (Finset.mem_insert_self _ _)))
    have he : idealLogNorm * finiteIdealMoebius (insert p S) =
        (idealLogNorm * finiteIdealMoebius S) * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, mul_sub, mul_one, map_sub, MvPowerSeries.X_def,
      MvPowerSeries.coeff_mul_monomial]
    simp only [Finsupp.single_le_iff, ite_eq_left hνp, mul_one]
    by_cases hSE : S = ∅
    · subst S
      simpa [finiteIdealMoebius] using idealLogNorm_prime_difference ν p hνp
    · have hS' : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSE
      have hνS : S ⊆ ν.support := fun q hq => hν (Finset.mem_insert_of_mem hq)
      have hνS' : S ⊆ (ν - Finsupp.single p 1 : EisensteinIdealExponent).support := by
        intro q hq
        apply Finsupp.mem_support_iff.mpr
        have hqp : q ≠ p := ne_of_mem_of_not_mem hq hp
        simpa [Finsupp.tsub_apply, hqp] using Finsupp.mem_support_iff.mp (hνS hq)
      rw [ih ν hS' hνS, ih _ hS' hνS', sub_self]
      have hc : (insert p S).card ≠ 1 := by
        rw [Finset.card_insert_of_notMem hp]
        have := Finset.card_pos.mpr hS'
        omega
      simp [hc]

lemma idealVonMangoldt_coeff_eq_finite (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      MvPowerSeries.coeff ν (idealLogNorm * finiteIdealMoebius ν.support) := by
  rw [idealVonMangoldt, mul_comm idealLogNorm, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hle : a.1 ≤ ν := by
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp ha]
    exact le_add_of_nonneg_right zero_le
  rw [coeff_idealMoebiusSeries_eq_finite ν.support a.1 (Finsupp.support_mono hle)]

/-- The von Mangoldt coefficient is supported precisely on prime-ideal
powers and has weight the logarithm of that prime-ideal norm. -/
lemma idealVonMangoldt_coeff (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      if ν.support.card = 1 then
        ∑ p ∈ ν.support, Real.log (normNat (idealPrimeRepresentative p)) else 0 := by
  rw [idealVonMangoldt_coeff_eq_finite]
  by_cases hs : ν.support.Nonempty
  · exact coeff_logNorm_finite_nonempty _ _ hs (Finset.Subset.refl _)
  · have hz : ν = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs)
    subst ν
    simp only [Finsupp.support_zero, finiteIdealMoebius, Finset.prod_empty, mul_one,
      Finset.card_empty, Nat.zero_ne_one, ite_false, if_false]
    change Real.log (idealExponentNorm 0) = 0
    simp [idealExponentNorm, idealExponentGenerator]

lemma idealVonMangoldt_not_prime_power (ν : EisensteinIdealExponent)
    (hν : ν.support.card ≠ 1) :
    MvPowerSeries.coeff ν idealVonMangoldt = 0 := by
  rw [idealVonMangoldt_coeff, ite_eq_right hν]

lemma idealVonMangoldt_coeff_nonneg (ν : EisensteinIdealExponent) :
    0 ≤ MvPowerSeries.coeff ν idealVonMangoldt := by
  rw [idealVonMangoldt_coeff]
  split_ifs
  · apply Finset.sum_nonneg
    intro p hp
    apply Real.log_nonneg
    simpa only [idealExponentNorm_single, pow_one] using
      idealExponentNorm_ge_one (Finsupp.single p 1)
  · exact le_rfl

lemma idealVonMangoldt_coeff_le_logNorm (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt ≤ Real.log (idealExponentNorm ν) := by
  by_cases hc : ν.support.card = 1
  · obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hc
    have hlog : 0 ≤ Real.log (normNat (idealPrimeRepresentative p)) := by
      apply Real.log_nonneg
      simpa only [idealExponentNorm_single, pow_one] using
        idealExponentNorm_ge_one (Finsupp.single p 1)
    have hn : (1 : ℝ) ≤ (ν p : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp
    rw [idealVonMangoldt_coeff, ite_eq_left hc, he, Finsupp.support_single _ hp,
      Finset.sum_singleton, idealExponentNorm_single, Real.log_pow]
    exact le_mul_of_one_le_left hlog hn
  · rw [idealVonMangoldt_not_prime_power ν hc]
    exact Real.log_nonneg (idealExponentNorm_ge_one ν)

lemma idealVonMangoldt_coeff_abs_le_logNorm (ν : EisensteinIdealExponent) :
    |MvPowerSeries.coeff ν idealVonMangoldt| ≤ Real.log (idealExponentNorm ν) := by
  rw [abs_of_nonneg (idealVonMangoldt_coeff_nonneg ν)]
  exact idealVonMangoldt_coeff_le_logNorm ν

lemma idealVonMangoldt_at_prime {a : Eisenstein} (ha : Prime a) :
    MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt = Real.log (norm a) := by
  have hcard : (idealExponentOf a).support.card = 1 := by
    rw [idealExponentOf_support_card ha.irreducible.squarefree,
      UniqueFactorizationMonoid.card_factors_of_irreducible ha.irreducible]
  obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hcard
  have hone : idealExponentOf a p = 1 := by
    have hle := (idealExponentOf_squarefree_iff ha.ne_zero).mpr ha.irreducible.squarefree p
    omega
  calc
    _ = MvPowerSeries.coeff (Finsupp.single p 1) idealVonMangoldt := by rw [he, hone]
    _ = Real.log (normNat (idealPrimeRepresentative p)) := idealVonMangoldt_prime_power p 0
    _ = Real.log (idealExponentNorm (idealExponentOf a)) := by
      rw [he, hone, idealExponentNorm_single, pow_one]
    _ = _ := by rw [idealExponentOf_norm ha.ne_zero]

/-- A nonzero von Mangoldt coefficient at an actual primary element
comes from an actual power of a primary prime, with no residual unit. -/
lemma idealVonMangoldt_primary_support {a : Eisenstein} (ha : primary a)
    (hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≠ 0) :
    ∃ p : Eisenstein, ∃ j : ℕ, primaryPrime p ∧ 0 < j ∧ a = p ^ j := by
  have hcard : (idealExponentOf a).support.card = 1 := by
    by_contra h
    exact hΛ (idealVonMangoldt_not_prime_power _ h)
  obtain ⟨p, hp, he⟩ := Finsupp.card_support_eq_one.mp hcard
  let j := idealExponentOf a p
  let r := idealPrimeRepresentative p
  have hj : 0 < j := Nat.pos_of_ne_zero hp
  have hgen : idealExponentGenerator (idealExponentOf a) = r ^ j := by
    rw [he]
    exact Finsupp.prod_single_index (h := fun q k => idealPrimeRepresentative q ^ k)
      (pow_zero _)
  have hassoc : Associated (r ^ j) a := by
    rw [← hgen]
    exact idealExponentOf_associated (primary_ne_zero ha)
  have hrdiv : r ∣ a := (dvd_pow_self r hj.ne').trans hassoc.dvd
  have hr : Prime r := (idealPrimeRepresentative_irreducible p).prime
  let q := primaryNormalize r
  have hq : primaryPrime q := ⟨primaryNormalize_primary
    (unit_residue_of_dvd_primary ha hrdiv), prime_primaryNormalize hr⟩
  have hqp : primary (q ^ j) := by
    induction j with
    | zero => simp [primary]
    | succ n ih => simpa only [pow_succ] using primary_mul ih hq.1
  refine ⟨q, j, hq, hj, ?_⟩
  apply primary_associated_eq ha hqp
  exact hassoc.symm.trans ((primaryNormalize_associated r).pow_pow (n := j))

lemma idealVonMangoldt_primary_nonprime_support {a : Eisenstein} (ha : primary a)
    (hprime : ¬ Prime a)
    (hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≠ 0) :
    ∃ p : Eisenstein, ∃ j : ℕ, primaryPrime p ∧ 2 ≤ j ∧ a = p ^ j := by
  obtain ⟨p,j,hp,hj,he⟩ := idealVonMangoldt_primary_support ha hΛ
  refine ⟨p,j,hp,?_,he⟩
  by_contra h
  have hje : j = 1 := by omega
  have hae : a = p := by simpa [hje] using he
  apply hprime
  rw [hae]
  exact hp.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedHecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite-order Hecke prime input

The finite-order Hecke prime-sum input specializes to independent prime
factors using the elementary character laws.

The input is the cubic-character consequence of Thorner--Zaman,
*A unified and improved Chebotarev density theorem*, Algebra & Number
Theory 13 (2019), Theorem 1.4, in the Siegel–Walfisz form for cubic Hecke characters.  Only finite-order characters occur in this input;
smooth weights and norm twists follow by partial summation.
-/

noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace CubicFirstMoment

/-- The character of an ordered tuple splits into the characters of its
individual factors. Repeated prime factors are still permitted here;
the squarefree restriction in the manuscript is imposed separately. -/
theorem mixedCubic_prod {ι : Type*} (s : Finset ι) (f : ι → Eisenstein)
    {q₁ q₂ : Eisenstein} (h₁ : primary q₁) (h₂ : primary q₂) :
    mixedCubic q₁ q₂ (∏ i ∈ s, f i) = ∏ i ∈ s, mixedCubic q₁ q₂ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mixedCubic_one h₁ h₂]
  | @insert i s hi ih => simp [hi, mixedCubic_mul h₁ h₂, ih]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem primaryIdealPolynomial_eq_elements (Y : ℝ) (A : EisensteinArithmeticFunction)
    (χ : Eisenstein → ℂ) :
    primaryIdealPolynomial Y A χ =
      ∑ a ∈ primaryElementBall Y, ((MvPowerSeries.coeff (idealExponentOf a) A : ℝ) : ℂ)*χ a := by
  unfold primaryIdealPolynomial primaryIdealBall
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    simp only [idealCharacterCoeff,idealPrimaryGenerator_at_element (mem_primaryElementBall.mp ha).1]
  · intro a ha b hb he
    have ha' := (mem_primaryElementBall.mp ha).1
    have hb' := (mem_primaryElementBall.mp hb).1
    have h := congrArg idealPrimaryGenerator he
    simpa only [idealPrimaryGenerator_at_element ha',idealPrimaryGenerator_at_element hb'] using h

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedAdditiveSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published additive large-sieve input over the Eisenstein integers

M. N. Huxley, *The large sieve inequality for algebraic number fields*,
Mathematika 15 (1968), 178–187. The precise imaginary-quadratic form used
here is displayed in P. Gao and L. Zhao, *The large sieve with power moduli
in imaginary quadratic number fields*, IJNT 18 (2022), 1713–1733,
arXiv:2101.00811v2, equation (1.2).

This is an explicit hypothesis type. The primitive multiplicative
character inequality is to be derived by finite Gauss expansion and
orthogonality; it is not assumed here.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma huxleyModulusMass_nonneg (q : Eisenstein) (N : Finset Eisenstein)
    (v : Eisenstein → ℂ) : 0 ≤ huxleyModulusMass q N v := by
  apply tsum_nonneg
  intro h
  split_ifs <;> positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramSchur
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite Gram row-sum bound

This is the linear algebra step in the exceptional-moment argument: a
symmetric absolute Gram kernel bounds its quadratic form by its largest
row sum. Both variables are retained in the estimate.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

theorem nonnegative_schur_bound {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (K : ι → ι → ℝ) (R : ℝ)
    (hK : ∀ p ∈ P, ∀ q ∈ P, 0 ≤ K p q)
    (hsym : ∀ p ∈ P, ∀ q ∈ P, K p q = K q p)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, K p q ≤ R) :
    (∑ p ∈ P, ∑ q ∈ P, x p * x q * K p q) ≤ R * ∑ p ∈ P, (x p)^2 := by
  have hpairs : (∑ p ∈ P, ∑ q ∈ P, 2 * (x p * x q * K p q)) ≤
      ∑ p ∈ P, ∑ q ∈ P, ((x p)^2 + (x q)^2) * K p q := by
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_le_sum
    intro q hq
    have h := mul_nonneg (sq_nonneg (x p-x q)) (hK p hp q hq)
    nlinarith only [h]
  have hswap : (∑ p ∈ P, ∑ q ∈ P, (x q)^2 * K p q) =
      ∑ p ∈ P, ∑ q ∈ P, (x p)^2 * K p q := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hsym q hq p hp]
  have hrow' : (∑ p ∈ P, ∑ q ∈ P, (x p)^2 * K p q) ≤
      R * ∑ p ∈ P, (x p)^2 := by
    simp only [← Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow p hp) (sq_nonneg (x p))
  have he : (∑ p ∈ P, ∑ q ∈ P, ((x p)^2 + (x q)^2) * K p q) =
      2 * ∑ p ∈ P, ∑ q ∈ P, (x p)^2 * K p q := by
    simp only [add_mul, Finset.sum_add_distrib]
    rw [hswap]
    ring
  rw [he] at hpairs
  simp only [← Finset.mul_sum] at hpairs hrow'
  linarith

/-- The complex Gram quadratic form is bounded using only absolute row
sums and Hermitian symmetry of their norms. -/
theorem complex_schur_bound {ι : Type*} (P : Finset ι) (z : ι → ℂ)
    (K : ι → ι → ℂ) (R : ℝ)
    (hsym : ∀ p ∈ P, ∀ q ∈ P, ‖K p q‖ = ‖K q p‖)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, ‖K p q‖ ≤ R) :
    ‖∑ p ∈ P, ∑ q ∈ P, z p * star (z q) * K p q‖ ≤
      R * ∑ p ∈ P, ‖z p‖^2 := by
  calc
    _ ≤ ∑ p ∈ P, ‖∑ q ∈ P, z p * star (z q) * K p q‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, ‖z p * star (z q) * K p q‖ :=
      Finset.sum_le_sum (fun p hp => norm_sum_le _ _)
    _ = ∑ p ∈ P, ∑ q ∈ P, ‖z p‖ * ‖z q‖ * ‖K p q‖ := by
      simp only [norm_mul, norm_star]
    _ ≤ _ := nonnegative_schur_bound P (fun p => ‖z p‖) (fun p q => ‖K p q‖) R
      (fun p hp q hq => _root_.norm_nonneg _) hsym hrow

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramOperator
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From Gram row sums to character-polynomial bounds

Finite duality turns the row-sum bound into an operator estimate. This is
the Cauchy/Gram step used after the multiplicity argument in the exceptional-character-moment argument.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

lemma complex_sum_norm_sq_expansion {ι : Type*} (P : Finset ι) (z : ι → ℂ) :
    ((‖∑ p ∈ P, z p‖^2 : ℝ) : ℂ) = ∑ p ∈ P, ∑ q ∈ P, z p * star (z q) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [starRingEnd_apply, star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma finiteGram_star {ι κ : Type*} (N : Finset κ) (T : ι → κ → ℂ) (p q : ι) :
    star (finiteGram N T q p) = finiteGram N T p q := by
  simp only [finiteGram, star_sum, star_mul, star_star]

lemma finite_gram_identity {ι κ : Type*} (P : Finset ι) (N : Finset κ)
    (z : ι → ℂ) (T : ι → κ → ℂ) :
    ((∑ n ∈ N, ‖∑ p ∈ P, z p * T p n‖^2 : ℝ) : ℂ) =
      ∑ p ∈ P, ∑ q ∈ P, z p * star (z q) * finiteGram N T p q := by
  have hcast : ((∑ n ∈ N, ‖∑ p ∈ P, z p * T p n‖^2 : ℝ) : ℂ) =
      ∑ n ∈ N, ((‖∑ p ∈ P, z p * T p n‖^2 : ℝ) : ℂ) :=
    map_sum Complex.ofRealHom _ _
  rw [hcast]
  simp_rw [complex_sum_norm_sq_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [finiteGram, Finset.mul_sum, star_mul]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem finite_gram_energy_le {ι κ : Type*} (P : Finset ι) (N : Finset κ)
    (z : ι → ℂ) (T : ι → κ → ℂ) (R : ℝ)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, ‖finiteGram N T p q‖ ≤ R) :
    (∑ n ∈ N, ‖∑ p ∈ P, z p * T p n‖^2) ≤ R * ∑ p ∈ P, ‖z p‖^2 := by
  have hs : ∀ p ∈ P, ∀ q ∈ P, ‖finiteGram N T p q‖ = ‖finiteGram N T q p‖ := by
    intro p hp q hq
    rw [← finiteGram_star N T p q, norm_star]
  have h := complex_schur_bound P z (finiteGram N T) R hs hrow
  rw [← finite_gram_identity P N z T, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at h
  exact h

/-- Duality exchanges rows and columns without loss. -/
theorem finite_gram_operator_le {ι κ : Type*} (P : Finset ι) (N : Finset κ)
    (v : κ → ℂ) (T : ι → κ → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, ‖finiteGram N T p q‖ ≤ R) :
    (∑ p ∈ P, ‖∑ n ∈ N, v n * T p n‖^2) ≤ R * ∑ n ∈ N, ‖v n‖^2 := by
  let f : ι → ℂ := fun p => ∑ n ∈ N, v n * T p n
  let g : κ → ℂ := fun n => ∑ p ∈ P, f p * star (T p n)
  let E : ℝ := ∑ p ∈ P, ‖f p‖^2
  let V : ℝ := ∑ n ∈ N, ‖v n‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdual : (E : ℂ) = ∑ n ∈ N, v n * star (g n) := by
    change ((∑ p ∈ P, ‖f p‖^2 : ℝ) : ℂ) = _
    have hcast : ((∑ p ∈ P, ‖f p‖^2 : ℝ) : ℂ) =
        ∑ p ∈ P, ((‖f p‖^2 : ℝ) : ℂ) := map_sum Complex.ofRealHom _ _
    rw [hcast]
    have he : ∀ p, ((‖f p‖^2 : ℝ) : ℂ) = f p * star (f p) := by
      intro p
      rw [Complex.ofReal_pow]
      exact (Complex.mul_conj' (f p)).symm
    simp_rw [he]
    conv_lhs => arg 2; ext p; lhs; unfold f
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [g, star_sum, star_mul, star_star, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hrow' : ∀ p ∈ P,
      ∑ q ∈ P, ‖finiteGram N (fun p n => star (T p n)) p q‖ ≤ R := by
    intro p hp
    have he : ∀ q, finiteGram N (fun p n => star (T p n)) p q = star (finiteGram N T p q) := by
      intro q
      simp only [finiteGram, star_sum, star_mul, star_star, mul_comm]
    simpa only [he, norm_star] using hrow p hp
  have hg := finite_gram_energy_le P N f (fun p n => star (T p n)) R hrow'
  change (∑ n ∈ N, ‖g n‖^2) ≤ R*E at hg
  have hc := complex_bilinear_rows_sq N v (fun n => star (g n))
  rw [← hdual, Complex.norm_real, Real.norm_of_nonneg hE] at hc
  simp only [norm_star] at hc
  change E^2 ≤ V * (∑ n ∈ N, ‖g n‖^2) at hc
  have hm := mul_le_mul_of_nonneg_left hg hV
  change E ≤ R*V
  by_cases hzero : E = 0
  · rw [hzero]
    exact mul_nonneg hR hV
  · have hpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
    nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MultiplicativeBessel
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite-character orthogonality step in the ordinary large sieve. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {R : Type*} [CommRing R] [Fintype R]

lemma mulChar_gram (χ ψ : MulChar R ℂ) :
    (∑ x : R, χ x*star (ψ x)) = if χ = ψ then (Fintype.card Rˣ:ℂ) else 0 := by
  simp_rw [MulChar.star_apply',← MulChar.mul_apply]
  by_cases h : χ = ψ
  · subst ψ
    rw [mul_inv_cancel,ite_eq_left rfl]
    exact MulChar.sum_one_eq_card_units
  · rw [ite_eq_right h]
    exact MulChar.sum_eq_zero_of_ne_one (fun he => h (mul_inv_eq_one.mp he))

/-- Bessel inequality for any selected finite set of distinct multiplicative
characters, with the exact unit-group cardinality. -/
theorem mulChar_bessel (C : Finset (MulChar R ℂ)) (v : R → ℂ) :
    (∑ χ ∈ C, ‖∑ x : R, v x*χ x‖^2) ≤
      (Fintype.card Rˣ:ℝ)*∑ x : R, ‖v x‖^2 := by
  apply finite_gram_operator_le C Finset.univ v (fun χ x => χ x)
    (show (0:ℝ) ≤ Fintype.card Rˣ by positivity)
  intro χ hχ
  change (∑ ψ ∈ C, ‖∑ x : R, χ x*star (ψ x)‖) ≤ _
  simp_rw [mulChar_gram]
  simp only [apply_ite, norm_zero, Complex.norm_natCast]
  simp [hχ]

/-- Gauss expansion transfers a character family to its additive sums
without a conductor loss. The hypotheses are finite Fourier identities,
not an analytic large-sieve estimate. -/
theorem gauss_transform_bessel {ι : Type*} (N : Finset ι)
    (C : Finset (MulChar R ℂ)) (v : ι → ℂ)
    (phase : R → ι → ℂ) (t : MulChar R ℂ → ι → ℂ)
    (g : MulChar R ℂ → ℂ)
    (hR : 0 < Fintype.card R)
    (hg : ∀ χ ∈ C, ‖g χ‖^2 = Fintype.card R)
    (htransform : ∀ χ ∈ C, ∀ n ∈ N,
      g χ*t χ n = ∑ x : R, χ x*phase x n) :
    (∑ χ ∈ C, ‖∑ n ∈ N, v n*t χ n‖^2) ≤
      ∑ x : R, ‖∑ n ∈ N, v n*phase x n‖^2 := by
  let S (x : R) := ∑ n ∈ N, v n*phase x n
  have hidentity (χ : MulChar R ℂ) (hχ : χ ∈ C) :
      g χ*(∑ n ∈ N, v n*t χ n) = ∑ x : R, S x*χ x := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ n ∈ N, v n*(∑ x : R, χ x*phase x n) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [← htransform χ hχ n hn]
        ring
      _ = _ := by
        simp only [S,Finset.mul_sum,Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro n hn
        ring
  have hbound := mulChar_bessel C S
  have he : (Fintype.card R:ℝ)*(∑ χ ∈ C, ‖∑ n ∈ N, v n*t χ n‖^2) =
      ∑ χ ∈ C, ‖∑ x : R, S x*χ x‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [← hidentity χ hχ,norm_mul,mul_pow,hg χ hχ]
  have hcard : Fintype.card Rˣ ≤ Fintype.card R :=
    Fintype.card_le_of_injective (fun x : Rˣ => (x:R)) Units.val_injective
  have hnonneg : 0 ≤ ∑ x : R, ‖S x‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hupper := hbound.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hnonneg)
  rw [← he] at hupper
  exact (mul_le_mul_iff_right₀ (by exact_mod_cast hR : (0:ℝ) < Fintype.card R)).mp hupper

/-- The same transfer with the additive side restricted to units. This is the
restriction appearing in the published additive large sieve. -/
theorem gauss_transform_unit_bessel {ι : Type*} (N : Finset ι)
    (C : Finset (MulChar R ℂ)) (v : ι → ℂ)
    (phase : R → ι → ℂ) (t : MulChar R ℂ → ι → ℂ)
    (g : MulChar R ℂ → ℂ)
    (hR : 0 < Fintype.card R)
    (hg : ∀ χ ∈ C, ‖g χ‖^2 = Fintype.card R)
    (htransform : ∀ χ ∈ C, ∀ n ∈ N,
      g χ*t χ n = ∑ x : R, χ x*phase x n) :
    (∑ χ ∈ C, ‖∑ n ∈ N, v n*t χ n‖^2) ≤
      ∑ x : R, if IsUnit x then ‖∑ n ∈ N, v n*phase x n‖^2 else 0 := by
  let phase' (x : R) (n : ι) := if IsUnit x then phase x n else 0
  have ht : ∀ χ ∈ C, ∀ n ∈ N, g χ*t χ n = ∑ x : R, χ x*phase' x n := by
    intro χ hχ n hn
    rw [htransform χ hχ n hn]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hu : IsUnit x
    · simp only [phase',hu,ite_true, if_true]
    · simp only [phase',hu,ite_false, if_false,MulChar.map_nonunit χ hu,zero_mul]
  have h := gauss_transform_bessel N C v phase' t g hR hg ht
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hu : IsUnit x <;> simp [phase',hu]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MixedCharacterSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conductor-by-conductor Gauss transfer for actual squarefree mixed characters. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_mixedGaussFactor {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hsa : Squarefree a) (hsb : Squarefree b) :
    ‖((Real.sqrt (norm (a*b)):ℂ)*(gauss a*star (gauss b)) / mixedCubic a b 3)‖^2 =
      norm (a*b) := by
  rw [norm_div,norm_mul,norm_mul,norm_star,norm_gauss_of_squarefree ha hsa,
    norm_gauss_of_squarefree hb hsb,
    mixedCubic_norm_of_coprime ha hb (primary_coprime_three (primary_mul ha hb))]
  simp only [mul_one,div_one,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (norm_nonneg _)

/-- Each actual primitive mixed cubic character is bounded by the unit-residue
additive energy at the same conductor. No analytic hypothesis is used. -/
theorem mixedCharacter_unit_energy (N : Finset Eisenstein) (v : Eisenstein → ℂ)
    {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hsa : Squarefree a) (hsb : Squarefree b) (hab : IsCoprime a b) :
    ‖∑ n ∈ N, v n*star (mixedCubic a b n)‖^2 ≤ huxleyModulusMass (a*b) N v := by
  have hq : a*b ≠ 0 := mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb)
  let : Finite (Residues (a*b)) := finite_residues hq
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  let χ := mixedResidueChar a b ha hb
  let phase (x : Residues (a*b)) (n : Eisenstein) :=
    huxleyPhase (a*b) (residueRepresentative (a*b) x) n
  let t (_ : MulChar (Residues (a*b)) ℂ) (n : Eisenstein) := star (mixedCubic a b n)
  let g (_ : MulChar (Residues (a*b)) ℂ) :=
    ((Real.sqrt (norm (a*b)):ℂ)*(gauss a*star (gauss b)) / mixedCubic a b 3)
  have hcard : (Fintype.card (Residues (a*b)):ℝ) = norm (a*b) := by
    rw [← Nat.card_eq_fintype_card,residues_card hq,normNat_cast]
  have hR : 0 < Fintype.card (Residues (a*b)) := by
    apply Nat.pos_of_ne_zero
    rw [← Nat.card_eq_fintype_card,residues_card hq]
    exact normNat_ne_zero hq
  have hg : ∀ ψ ∈ ({χ} : Finset (MulChar (Residues (a*b)) ℂ)),
      ‖g ψ‖^2 = Fintype.card (Residues (a*b)) := by
    intro ψ hψ
    rw [hcard]
    exact norm_mixedGaussFactor ha hb hsa hsb
  have ht : ∀ ψ ∈ ({χ} : Finset (MulChar (Residues (a*b)) ℂ)), ∀ n ∈ N,
      g ψ*t ψ n = ∑ x : Residues (a*b), ψ x*phase x n := by
    intro ψ hψ n hn
    have he : ψ = χ := Finset.mem_singleton.mp hψ
    subst ψ
    exact (mixedResidueChar_fourier ha hb hsa hsb hab n).symm
  have h := gauss_transform_unit_bessel N {χ} v phase t g hR hg ht
  simp only [Finset.sum_singleton,t] at h
  refine h.trans_eq ?_
  rw [huxleyModulusMass,tsum_fintype]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hu : IsUnit x <;> simp [hu,phase,additiveSievePolynomial]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OrdinaryMixedSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary mixed cubic character sieve, derived from Huxley's additive
large sieve. The only extra loss is the proved arbitrarily small divisor power. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma pairConductor_primary {p : Eisenstein × Eisenstein} (hp : PrimarySquarefreePair p) :
    primary (pairConductor p) := primary_mul hp.1 hp.2.1

lemma pairConductor_squarefree {p : Eisenstein × Eisenstein} (hp : PrimarySquarefreePair p) :
    Squarefree (pairConductor p) := squarefree_mul_iff.mpr ⟨hp.2.2.2.2.isRelPrime,hp.2.2.1,hp.2.2.2.1⟩

/-- A product determines the second factor, so conductor multiplicity is at
most the number of primary squarefree divisors. -/
lemma pairConductor_fiber_card (P : Finset (Eisenstein × Eisenstein))
    (hP : ∀ p ∈ P, PrimarySquarefreePair p) {q : Eisenstein} (hq : primary q) :
    ((P.filter (fun p => pairConductor p = q)).card : ℝ) ≤
      (2:ℝ)^(primaryPrimeFactors q).card := by
  let F := P.filter (fun p => pairConductor p = q)
  let T := P.image Prod.fst
  have hinj : Set.InjOn Prod.fst (↑F : Set (Eisenstein × Eisenstein)) := by
    intro x hx y hy he
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    apply Prod.ext he
    apply mul_left_cancel₀ (primary_ne_zero (hP x hx'.1).1)
    calc
      x.1*x.2 = q := hx'.2
      _ = y.1*y.2 := hy'.2.symm
      _ = x.1*y.2 := by rw [he]
  have hT : ∀ a ∈ T, primary a ∧ Squarefree a := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨(hP p hp).1,(hP p hp).2.2.1⟩
  have hsub : F.image Prod.fst ⊆ T.filter (· ∣ q) := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hp'.1,
      hp'.2 ▸ dvd_mul_right p.1 p.2⟩
  calc
    (F.card:ℝ) = ((F.image Prod.fst).card:ℝ) := by rw [Finset.card_image_iff.mpr hinj]
    _ ≤ ((T.filter (· ∣ q)).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := primary_divisors_card_le T hT hq

/-- Finite collection of the single-conductor energy inequalities. -/
theorem mixedCharacter_energy_collection {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℝ) (N : Finset Eisenstein)
      (P : Finset (Eisenstein × Eisenstein)), 1 ≤ Q →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ n ∈ N, v n*star (mixedCubic p.1 p.2 n)‖^2) ≤
        K*Q^ε*∑ q ∈ nonzeroNormBall Q, huxleyModulusMass q N v := by
  obtain ⟨K,hK,hweight⟩ := primeDivisorWeight_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro Q N P hQ hP v
  have hmaps : ∀ p ∈ P, pairConductor p ∈ nonzeroNormBall Q := by
    intro p hp
    exact mem_nonzeroNormBall.mpr ⟨(hP p hp).2,
      primary_ne_zero (pairConductor_primary (hP p hp).1)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  let F := P.filter (fun p => pairConductor p = q)
  by_cases hF : F.Nonempty
  · obtain ⟨p,hp⟩ := hF
    have hp' := Finset.mem_filter.mp hp
    have hqp : primary q := hp'.2 ▸ pairConductor_primary (hP p hp'.1).1
    have hqs : Squarefree q := hp'.2 ▸ pairConductor_squarefree (hP p hp'.1).1
    have hqn : norm q ≤ Q := by rw [← hp'.2]; exact (hP p hp'.1).2
    have hcard : (F.card:ℝ) ≤ K*Q^ε :=
      (pairConductor_fiber_card P (fun p hp => (hP p hp).1) hqp).trans
        ((hweight q hqp hqs).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg q) hqn hε.le) hK.le))
    calc
      _ ≤ ∑ _p ∈ F, huxleyModulusMass q N v := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hh := (hP p hp'.1).1
        have hb := mixedCharacter_unit_energy N v hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2
        simpa only [← hp'.2,pairConductor] using hb
      _ = (F.card:ℝ)*huxleyModulusMass q N v := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (huxleyModulusMass_nonneg q N v)
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (∑ p ∈ F, _) ≤ _
    rw [he,Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (by linarith) _))
      (huxleyModulusMass_nonneg q N v)

/-- The ordinary large sieve for actual squarefree coprime cubic pairs. Its
sole analytic hypothesis is the cited additive `Q²+Z` inequality. -/
theorem ordinary_mixed_cubic_sieve (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q Z : ℝ, 1 ≤ Q → 1 ≤ Z →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ n ∈ nonzeroNormBall Z, v n*star (mixedCubic p.1 p.2 n)‖^2) ≤
        C*Q^ε*(Q^2+Z)*∑ n ∈ nonzeroNormBall Z, ‖v n‖^2 := by
  obtain ⟨K,hK,hcollect⟩ := mixedCharacter_energy_collection hε
  obtain ⟨H,hH,hadd⟩ := hHuxley
  refine ⟨K*H,mul_pos hK hH,?_⟩
  intro Q Z hQ hZ P hP v
  apply (hcollect Q (nonzeroNormBall Z) P hQ hP v).trans
  have hh := mul_le_mul_of_nonneg_left (hadd Q Z hQ hZ v)
    (mul_nonneg hK.le (Real.rpow_nonneg (show 0 ≤ Q by linarith) ε))
  dsimp only [huxleySieveMass] at hh
  convert hh using 1 <;> first | rfl | ring

/-- Conjugating the coefficients gives the other character orientation. -/
theorem ordinary_mixed_cubic_sieve_unstar (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q Z : ℝ, 1 ≤ Q → 1 ≤ Z →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ n ∈ nonzeroNormBall Z, v n*mixedCubic p.1 p.2 n‖^2) ≤
        C*Q^ε*(Q^2+Z)*∑ n ∈ nonzeroNormBall Z, ‖v n‖^2 := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_cubic_sieve hHuxley hε
  refine ⟨C,hC,?_⟩
  intro Q Z hQ hZ P hP v
  have h := hbound Q Z hQ hZ P hP (fun n => star (v n))
  simpa only [← star_mul,← star_sum,norm_star,mul_comm] using h

/-- Restriction to an arbitrary finite coefficient support costs nothing. -/
theorem ordinary_mixed_cubic_sieve_finite (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q Z : ℝ, 1 ≤ Q → 1 ≤ Z →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (B : Finset Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ b ∈ B, b ≠ 0 ∧ norm b ≤ Z) → ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ n ∈ B, v n*mixedCubic p.1 p.2 n‖^2) ≤
        C*Q^ε*(Q^2+Z)*∑ n ∈ B, ‖v n‖^2 := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_cubic_sieve_unstar hHuxley hε
  refine ⟨C,hC,?_⟩
  intro Q Z hQ hZ P B hP hB v
  let w (n : Eisenstein) := if n ∈ B then v n else 0
  have hsub : B ⊆ nonzeroNormBall Z := fun n hn =>
    mem_nonzeroNormBall.mpr ⟨(hB n hn).2,(hB n hn).1⟩
  have hsum (p : Eisenstein × Eisenstein) :
      (∑ n ∈ nonzeroNormBall Z, w n*mixedCubic p.1 p.2 n) =
        ∑ n ∈ B, v n*mixedCubic p.1 p.2 n := by
    rw [← Finset.sum_subset hsub (fun n _ hn => by simp [w,hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [w,hn,ite_true, if_true]
  have henergy : (∑ n ∈ nonzeroNormBall Z, ‖w n‖^2) = ∑ n ∈ B, ‖v n‖^2 := by
    rw [← Finset.sum_subset hsub (fun n _ hn => by simp [w,hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [w,hn,ite_true, if_true]
  simpa only [hsum,henergy] using hbound Q Z hQ hZ P hP w

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PolynomialMeanValue
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ordinary mean values after collecting Eisenstein norms

The input `MontgomeryVaughanBound` is the ordinary Dirichlet-polynomial
mean-square theorem of Montgomery--Vaughan, *Hilbert's inequality*,
J. London Math. Soc. (2) 8 (1974), Corollary 3, p. 75, equation (1.11),
in the form explicitly recorded
in the manuscript as `eq:ordinary-mean-value`.

The deductions below collect the actual Eisenstein norms, record their
multiplicity cost, and preserve an arbitrary fixed angular weight and
an arbitrary translated height. These are the ordinary mean-value steps
in `eq:dispersion-height-small` and `eq:angular-completed-height`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

lemma mellinPhase_add (t u x : ℝ) :
    mellinPhase (t + u) x = mellinPhase t x * mellinPhase u x := by
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeSquareSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse support from a large square divisor, used to remove repeated
large primes in the exceptional character moments. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma square_multiples_normBall {Y : ℝ} {d b : Eisenstein}
    (hd : d ≠ 0) (hb : b ∈ nonzeroNormBall Y) (hdiv : d^2 ∣ b) :
    b ∈ (nonzeroNormBall (Y/(norm d)^2)).image (fun c => d^2*c) := by
  obtain ⟨c,rfl⟩ := hdiv
  have hspec := mem_nonzeroNormBall.mp hb
  have hc : c ≠ 0 := by intro h; simp [h] at hspec
  have hnorm : norm (d^2*c) = (norm d)^2*norm c := by
    simp [pow_two,mul_assoc]
  apply Finset.mem_image.mpr
  refine ⟨c,mem_nonzeroNormBall.mpr ⟨?_,hc⟩,rfl⟩
  apply (le_div_iff₀ (sq_pos_of_pos (norm_pos_of_ne_zero hd))).mpr
  have h := hspec.1
  rw [hnorm] at h
  nlinarith

/-- Cardinality is at most `C Y / sqrt D`, uniformly for positive `D`.
The proof uses only planar lattice counting and a convergent norm series. -/
theorem largeSquareSupport_card_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Y D : ℝ, 0 ≤ Y → 0 < D →
      ((largeSquareSupport Y D).card:ℝ) ≤ C*Y*D^(-(1/2:ℝ)) := by
  let Z := ∑' d : Eisenstein, norm d^(-(3/2:ℝ))
  have hZ : 0 ≤ Z := tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  refine ⟨18*Z+1,by positivity,?_⟩
  intro Y D hY hD
  let T := (nonzeroNormBall Y).filter (fun d => D < norm d)
  let F (d : Eisenstein) := (nonzeroNormBall (Y/(norm d)^2)).image (fun c => d^2*c)
  have hcover : largeSquareSupport Y D ⊆ T.biUnion F := by
    intro b hb
    obtain ⟨hball,d,hd,hdiv⟩ := Finset.mem_filter.mp hb
    have hd0 : d ≠ 0 := norm_eq_zero_iff.not.mp (ne_of_gt (hD.trans hd))
    have hdvd : d ∣ b := (dvd_pow_self d (by norm_num : 2 ≠ 0)).trans hdiv
    have hdb : norm d ≤ norm b := norm_le_of_dvd (mem_nonzeroNormBall.mp hball).2 hdvd
    apply Finset.mem_biUnion.mpr
    refine ⟨d,Finset.mem_filter.mpr ⟨mem_nonzeroNormBall.mpr
      ⟨hdb.trans (mem_nonzeroNormBall.mp hball).1,hd0⟩,hd⟩,?_⟩
    exact square_multiples_normBall hd0 hball hdiv
  have hcard : ((largeSquareSupport Y D).card:ℝ) ≤ ∑ d ∈ T, ((F d).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hsum : (∑ d ∈ T, 1/(norm d)^2) ≤ D^(-(1/2:ℝ))*Z := by
    have htail := eisenstein_norm_rpow_tail (s := (3/2:ℝ)) (t := 2) hD
      (by norm_num) (by norm_num)
    norm_num only at htail
    apply le_trans _ htail
    have hs := (summable_eisenstein_norm_rpow (s := 2) (by norm_num)).indicator
      (fun d => D < norm d)
    calc
      _ = ∑ d ∈ T, if D < norm d then norm d^(-(2:ℝ)) else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hn := (Finset.mem_filter.mp hd).2
        rw [ite_eq_left hn,Real.rpow_neg (norm_nonneg d),Real.rpow_two,one_div]
      _ ≤ _ := hs.sum_le_tsum T (fun d _ => by
        split_ifs
        · exact Real.rpow_nonneg (norm_nonneg d) _
        · exact le_rfl)
  calc
    _ ≤ ∑ d ∈ T, ((F d).card:ℝ) := hcard
    _ ≤ ∑ d ∈ T, 18*(Y/(norm d)^2) := by
      apply Finset.sum_le_sum
      intro d hd
      have hi : ((F d).card:ℝ) ≤ ((nonzeroNormBall (Y/(norm d)^2)).card:ℝ) := by
        exact_mod_cast Finset.card_image_le
      exact hi.trans (nonzeroNormBall_card_le (by positivity))
    _ = 18*Y*(∑ d ∈ T, 1/(norm d)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 18*Y*(D^(-(1/2:ℝ))*Z) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := by nlinarith [Real.rpow_nonneg hD.le (-(1/2:ℝ))]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- Removing nonsquarefree products never enlarges a coefficient; its
error also obeys the same uniform coefficient bound. -/
theorem convolutionError_norm_bound (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (M : ι → ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (hM : ∀ i, 0 ≤ M i) (hw : ∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i)
    (b : Eisenstein) :
    ‖orderedConvolution S w b-squarefreeConvolution S w b‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  by_cases hs : Squarefree b
  · simp only [squarefreeConvolution,ite_eq_left hs,sub_self,norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))
  · simpa only [squarefreeConvolution,ite_eq_right hs,sub_zero] using
      orderedConvolution_norm_bound S w M hS hM hw b

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean values of the squarefree prime-convolution discrepancy

The ordinary Montgomery--Vaughan input is specialized to the actual
coefficients obtained from independent prime factors.  The full polynomial
factors exactly; removing repeated primes costs the energy already proved
in `RepeatedPrimeSupport`.  The maximum multiplicity of an integer norm is
kept explicit, so no divisor estimate is hidden in this deduction.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A character bounded by one does not increase coefficient energy,
including at primes dividing its conductor, where it may vanish. -/
lemma coefficient_twist_energy_le (B : Finset Eisenstein)
    (β χ : Eisenstein → ℂ) (hχ : ∀ b ∈ B, ‖χ b‖ ≤ 1) :
    (∑ b ∈ B, ‖β b * χ b‖ ^ 2) ≤ ∑ b ∈ B, ‖β b‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro b hb
  apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
  rw [norm_mul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (hχ b hb) (_root_.norm_nonneg (β b))

lemma norm_mixedCubic_le_one {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) (b : Eisenstein) :
    ‖mixedCubic q₁ q₂ b‖ ≤ 1 := by
  rw [mixedCubic, norm_mul, norm_star]
  simpa only [mul_one] using
    mul_le_mul (norm_cubicSymbol_le_one h₁ b) (norm_cubicSymbol_le_one h₂ b)
      (_root_.norm_nonneg _) zero_le_one

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseFourthMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square of a structured error polynomial has controlled coefficient
energy. This supplies the fourth-moment estimate in the balanced range. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma second_moment_sq_le_card_fourth {ι : Type*} (P : Finset ι) (v : ι → ℂ) :
    (∑ p ∈ P, ‖v p‖^2)^2 ≤ (P.card:ℝ)*∑ p ∈ P, ‖v p‖^4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq P (fun _ => (1:ℝ)) (fun p => ‖v p‖^2)
  simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,← pow_mul] using h

lemma squareConvolution_character (B : Finset Eisenstein) (v χ : Eisenstein → ℂ)
    (hχ : ∀ a b, χ (a*b) = χ a*χ b) :
    (∑ n ∈ productSupport B, squareConvolution B v n*χ n) =
      (∑ b ∈ B, v b*χ b)^2 := by
  unfold squareConvolution productSupport
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ n ∈ (B.product B).image (fun z => z.1*z.2),
        ∑ z ∈ B.product B with z.1*z.2 = n, (v z.1*v z.2)*χ (z.1*z.2) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro z hz
      rw [(Finset.mem_filter.mp hz).2]
    _ = ∑ z ∈ B.product B, (v z.1*v z.2)*χ (z.1*z.2) :=
      Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem _ hz) _
    _ = _ := by
      rw [Finset.product_eq_sprod,Finset.sum_product B B _,pow_two,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [hχ]
      ring

lemma squareConvolution_energy (B : Finset Eisenstein) (v : Eisenstein → ℂ)
    {K : ℝ} (hK : ∀ n ∈ productSupport B,
      (((B.product B).filter (fun z => z.1*z.2 = n)).card:ℝ) ≤ K) :
    (∑ n ∈ productSupport B, ‖squareConvolution B v n‖^2) ≤
      K*(∑ b ∈ B, ‖v b‖^2)^2 := by
  have hrow (n : Eisenstein) (hn : n ∈ productSupport B) :
      ‖squareConvolution B v n‖^2 ≤
        K * ∑ z ∈ B.product B with z.1*z.2 = n, ‖v z.1*v z.2‖^2 := by
    let T := (B.product B).filter (fun z => z.1*z.2 = n)
    have hc := complex_bilinear_rows_sq T (fun _ => (1:ℂ)) (fun z => v z.1*v z.2)
    simp only [one_mul,norm_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right (hK n hn)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  calc
    _ ≤ ∑ n ∈ productSupport B,
        K * ∑ z ∈ B.product B with z.1*z.2 = n, ‖v z.1*v z.2‖^2 :=
      Finset.sum_le_sum hrow
    _ = K * ∑ z ∈ B.product B, ‖v z.1*v z.2‖^2 := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem _ hz) _
    _ = _ := by
      simp only [norm_mul,mul_pow]
      rw [Finset.product_eq_sprod,Finset.sum_product B B _]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul,pow_two]

/-- Apply the ordinary character sieve to the actual squared polynomial.
The input multiplicity is purely arithmetic and is discharged below for
bounded-length products of primes. -/
theorem ordinary_mixed_fourth_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q Z : ℝ), 1 ≤ Q → 1 ≤ Z →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (B : Finset Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ b ∈ B, b ≠ 0 ∧ norm b ≤ Z) →
      ∀ (K : ℝ), (∀ n ∈ productSupport B,
        (((B.product B).filter (fun z => z.1*z.2 = n)).card:ℝ) ≤ K) →
      ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^4) ≤
        C*Q^ε*(Q^2+Z^2)*K*(∑ b ∈ B, ‖v b‖^2)^2 := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_cubic_sieve_finite hHuxley hε
  refine ⟨C,hC,?_⟩
  intro Q Z hQ hZ P B hP hB K hK v
  have hBB : ∀ n ∈ productSupport B, n ≠ 0 ∧ norm n ≤ Z^2 := by
    intro n hn
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    refine ⟨mul_ne_zero (hB a ha).1 (hB b hb).1,?_⟩
    rw [norm_mul_eq,pow_two]
    exact mul_le_mul (hB a ha).2 (hB b hb).2 (norm_nonneg b) (by linarith)
  have he (p : Eisenstein × Eisenstein) (hp : p ∈ P) :
      ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^4 =
      ‖∑ n ∈ productSupport B, squareConvolution B v n*mixedCubic p.1 p.2 n‖^2 := by
    rw [squareConvolution_character B v _ (mixedCubic_mul (hP p hp).1.1 (hP p hp).1.2.1),
      norm_pow]
    ring
  calc
    _ = ∑ p ∈ P, ‖∑ n ∈ productSupport B,
        squareConvolution B v n*mixedCubic p.1 p.2 n‖^2 := Finset.sum_congr rfl he
    _ ≤ C*Q^ε*(Q^2+Z^2)*∑ n ∈ productSupport B, ‖squareConvolution B v n‖^2 :=
      hbound Q (Z^2) hQ (one_le_pow₀ hZ) P (productSupport B) hP hBB _
    _ ≤ C*Q^ε*(Q^2+Z^2)*(K*(∑ b ∈ B, ‖v b‖^2)^2) :=
      mul_le_mul_of_nonneg_left (squareConvolution_energy B v hK) (by positivity)
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueIdealCharacters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma residueIdealChar_add (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ν κ : EisensteinIdealExponent) :
    residueIdealChar q χ (ν+κ) = residueIdealChar q χ ν*residueIdealChar q χ κ := by
  simp only [residueIdealChar,idealExponentGenerator_add,map_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeckeCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma angularResidueIdealChar_add (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (ν κ : EisensteinIdealExponent) :
    angularResidueIdealChar q χ ℓ (ν+κ) =
      angularResidueIdealChar q χ ℓ ν*angularResidueIdealChar q χ ℓ κ := by
  simp only [angularResidueIdealChar, residueIdealChar_add, idealExponentGenerator_add, theta_mul]
  ring

lemma angular_character_associated {q x y : Eisenstein}
    (χ : MulChar (Residues q) ℂ) {ℓ : ℤ} (hu : AngularUnitCompatible q χ ℓ)
    (hxy : Associated x y) :
    χ (Ideal.Quotient.mk (modulus q) x)*theta ℓ x =
      χ (Ideal.Quotient.mk (modulus q) y)*theta ℓ y := by
  obtain ⟨u,rfl⟩ := hxy
  rw [map_mul, map_mul, theta_mul]
  symm
  calc
    _ = (χ (Ideal.Quotient.mk (modulus q) x)*theta ℓ x)*
        (χ (Ideal.Quotient.mk (modulus q) u)*theta ℓ u) := by ring
    _ = _ := by rw [hu u, mul_one]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryConvolutionEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- The tuple multiplicity is uniformly a small power even when each
factor has arbitrarily many distinct prime divisors. -/
theorem primary_tuple_fiber_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein),
      (∀ i, ∀ a ∈ S i, primary a) → ∀ Y : ℝ, 1 ≤ Y →
      ∀ b ∈ orderedConvolutionSupport S, norm b ≤ Y →
      (((Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)).card : ℝ) ≤ C*Y^ε := by
  let k : ℝ := Fintype.card ι
  let δ : ℝ := ε/(k+1)
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδε : δ*k ≤ ε := by
    have h := div_mul_cancel₀ ε (show k+1 ≠ 0 by positivity)
    change δ*(k+1) = ε at h
    nlinarith
  obtain ⟨D,hD,hdiv⟩ := primary_divisor_card_small_power hδ
  refine ⟨D^(Fintype.card ι),pow_pos hD _,?_⟩
  intro S hS Y hY b hb hbY
  have hb0 := primary_ne_zero (orderedPrimarySupport_primary S hS hb)
  have hsub : (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b) ⊆
      Fintype.piFinset (fun i => (S i).filter (fun a => a ∣ b)) := by
    intro f hf
    obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
    apply Fintype.mem_piFinset.mpr
    intro i
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hfs i,?_⟩
    rw [← hfb]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  have hcard (i : ι) : (((S i).filter (fun a => a ∣ b)).card : ℝ) ≤ D*Y^δ :=
    (hdiv (S i) (hS i) b hb0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg b) hbY hδ.le) hD.le)
  calc
    _ ≤ ((Fintype.piFinset (fun i => (S i).filter (fun a => a ∣ b))).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = ∏ i, (((S i).filter (fun a => a ∣ b)).card : ℝ) := by
      rw [Fintype.card_piFinset,Nat.cast_prod]
    _ ≤ ∏ _i : ι, D*Y^δ := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
      (fun i _ => hcard i)
    _ = D^(Fintype.card ι)*Y^(δ*k) := by
      rw [Finset.prod_const,Finset.card_univ,mul_pow,← Real.rpow_mul_natCast (by linarith)]
    _ ≤ D^(Fintype.card ι)*Y^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hY hδε) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedErrorMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The repeated-prime discrepancy is negligible in the balanced
exceptional family. Both its fourth moment and the number of rows are
derived from the actual finite supports. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma balanced_pair_card (P : Finset (Eisenstein × Eisenstein)) {L : ℝ}
    (hL : 0 ≤ L) (hP : ∀ p ∈ P, primary p.1 ∧ primary p.2 ∧
      norm p.1 ≤ L ∧ norm p.2 ≤ L) : (P.card:ℝ) ≤ 324*L^2 := by
  have hsub : P ⊆ (nonzeroNormBall L).product (nonzeroNormBall L) := by
    intro p hp
    obtain ⟨hp₁,hp₂,hN₁,hN₂⟩ := hP p hp
    exact Finset.mem_product.mpr ⟨mem_nonzeroNormBall.mpr ⟨hN₁,primary_ne_zero hp₁⟩,
      mem_nonzeroNormBall.mpr ⟨hN₂,primary_ne_zero hp₂⟩⟩
  calc
    (P.card:ℝ) ≤ ((nonzeroNormBall L).card:ℝ)^2 := by
      have h := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
      simpa only [Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul,pow_two] using h
    _ ≤ (18*L)^2 := pow_le_pow_left₀ (by positivity) (nonzeroNormBall_card_le hL) 2
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Higher prime powers in the von Mangoldt replacement have sparse support,
even when the underlying prime is small. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primePower_norm_pow (p : Eisenstein) (j : ℕ) : norm (p^j) = norm p^j := by
  induction j with
  | zero => simp [norm]
  | succ j ih => rw [pow_succ,norm_mul_eq,ih,pow_succ]

/-- Extracting half the exponent produces a genuinely large square divisor.
The bound depends on the prime-power norm, not the prime norm. -/
lemma large_square_of_prime_power {p b : Eisenstein} (hp : p ≠ 0) {j : ℕ}
    (hj : 2 ≤ j) {Y c : ℝ} (hY : 0 < Y)
    (hlarge : Y^c < norm (p^j)) (hdiv : p^j ∣ b) :
    ∃ d : Eisenstein, Y^(c/4) < norm d ∧ d^2 ∣ b := by
  refine ⟨p^(j/2),?_,?_⟩
  · have he : j ≤ 4*(j/2) := by omega
    have hpow : norm (p^j) ≤ norm (p^(j/2))^4 := by
      rw [primePower_norm_pow,primePower_norm_pow,← pow_mul]
      rw [Nat.mul_comm (j/2) 4]
      exact pow_le_pow_right₀ (one_le_norm hp) he
    have hYpow : (Y^(c/4))^4 = Y^c := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hY.le]
      congr 1
      norm_num
    by_contra! hn
    have hd := pow_le_pow_left₀ (norm_nonneg _) hn 4
    rw [hYpow] at hd
    exact (hlarge.trans_le hpow).not_ge hd
  · apply dvd_trans _ hdiv
    rw [← pow_mul]
    exact pow_dvd_pow p (by omega)

lemma largePrimePowerSupport_subset {Y c : ℝ} (hY : 0 < Y) :
    largePrimePowerSupport Y c ⊆ largeSquareSupport Y (Y^(c/4)) := by
  intro b hb
  obtain ⟨hball,p,j,hp,hj,hlarge,hdiv⟩ := Finset.mem_filter.mp hb
  obtain ⟨d,hd,hdvd⟩ := large_square_of_prime_power hp.2.ne_zero hj hY hlarge hdiv
  exact Finset.mem_filter.mpr ⟨hball,d,hd,hdvd⟩

/-- A fixed positive power is saved for every higher-prime-power error support. -/
theorem largePrimePowerSupport_card_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y c : ℝ), 0 < Y →
      ((largePrimePowerSupport Y c).card:ℝ) ≤ K*Y^(1-c/8) := by
  obtain ⟨K,hK,hbound⟩ := largeSquareSupport_card_bound
  refine ⟨K,hK,?_⟩
  intro Y c hY
  have h := hbound Y (Y^(c/4)) hY.le (Real.rpow_pos_of_pos hY _)
  have hcard : ((largePrimePowerSupport Y c).card:ℝ) ≤
      ((largeSquareSupport Y (Y^(c/4))).card:ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (largePrimePowerSupport_subset hY))
  have he : K*Y*(Y^(c/4))^(-(1/2:ℝ)) = K*Y^(1-c/8) := by
    rw [mul_assoc]
    congr 1
    calc
      _ = Y^(1:ℝ)*Y^(c/4*(-(1/2:ℝ))) := by
        rw [Real.rpow_one,← Real.rpow_mul hY.le]
      _ = Y^(1+c/4*(-(1/2:ℝ))) := (Real.rpow_add hY _ _).symm
      _ = _ := by congr 1; ring
  exact hcard.trans (h.trans_eq he)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimitiveDualMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubic second moments for the actual primitive ideal characters.
The primes above three are separated exactly before applying the cubic sieve. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angularResidueIdealChar_primaryNormalize {d : Eisenstein}
    (ψ : MulChar (Residues d) ℂ) {ℓ : ℤ} (hu : AngularUnitCompatible d ψ ℓ)
    (ν : EisensteinIdealExponent) :
    angularResidueIdealChar d ψ ℓ ν =
      ψ (Ideal.Quotient.mk (modulus d) (idealPrimaryGenerator ν))*
        theta ℓ (idealPrimaryGenerator ν) :=
  angular_character_associated ψ hu
    (primaryNormalize_associated (idealExponentGenerator ν))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusProducts
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short Möbius identity remains valid inside any fixed product of
prime-weight factors. This is the algebraic replacement before smoothing. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma shortVonMangoldt_two_four (F : ℝ) :
    shortVonMangoldt F = 2*shortTwoFactor F-shortFourFactor F := by
  unfold shortVonMangoldt shortTwoFactor shortFourFactor
  ring

lemma shortVonMangoldt_local {F : ℝ} (hF : 0 ≤ F) :
    NormLocalEq F idealVonMangoldt (shortVonMangoldt F) :=
  fun ν hν => short_moebius_identity hF ν hν

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularArithmeticTwist
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Twisting actual ideal arithmetic functions by a residue character and
norm phase commutes with convolution. Different original factors may
therefore retain different Mellin heights throughout short inversion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

lemma angularResidueNormTwist_add (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (ν κ : EisensteinIdealExponent) :
    angularResidueNormTwist ℓ q η t (ν+κ) = angularResidueNormTwist ℓ q η t ν*angularResidueNormTwist ℓ q η t κ := by
  rw [angularResidueNormTwist,angularResidueIdealChar_add,idealExponentNorm_add,
    mellinPhase_mul_pos t (idealExponentNorm_pos ν) (idealExponentNorm_pos κ)]
  unfold angularResidueNormTwist
  ring

lemma angularTwistArithmetic_mul (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A B : EisensteinArithmeticFunction) :
    angularTwistArithmetic ℓ q η t (A*B) = angularTwistArithmetic ℓ q η t A*angularTwistArithmetic ℓ q η t B := by
  apply MvPowerSeries.ext
  intro ν
  change ((MvPowerSeries.coeff ν (A*B):ℝ):ℂ)*angularResidueNormTwist ℓ q η t ν = _
  rw [MvPowerSeries.coeff_mul,Complex.ofReal_sum,Finset.sum_mul,MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  change ((MvPowerSeries.coeff p.1 A*MvPowerSeries.coeff p.2 B:ℝ):ℂ)*
      angularResidueNormTwist ℓ q η t ν = _
  rw [← he,angularResidueNormTwist_add ℓ,Complex.ofReal_mul]
  change _ = (((MvPowerSeries.coeff p.1 A:ℝ):ℂ)*angularResidueNormTwist ℓ q η t p.1)*
    (((MvPowerSeries.coeff p.2 B:ℝ):ℂ)*angularResidueNormTwist ℓ q η t p.2)
  ring

lemma angularTwistArithmetic_add (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A B : EisensteinArithmeticFunction) :
    angularTwistArithmetic ℓ q η t (A+B) = angularTwistArithmetic ℓ q η t A+angularTwistArithmetic ℓ q η t B := by
  ext ν
  change ((MvPowerSeries.coeff ν (A+B):ℝ):ℂ)*angularResidueNormTwist ℓ q η t ν =
    ((MvPowerSeries.coeff ν A:ℝ):ℂ)*angularResidueNormTwist ℓ q η t ν +
      ((MvPowerSeries.coeff ν B:ℝ):ℂ)*angularResidueNormTwist ℓ q η t ν
  rw [map_add,Complex.ofReal_add,add_mul]

lemma angularTwistArithmetic_sub (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A B : EisensteinArithmeticFunction) :
    angularTwistArithmetic ℓ q η t (A-B) = angularTwistArithmetic ℓ q η t A-angularTwistArithmetic ℓ q η t B := by
  ext ν
  change ((MvPowerSeries.coeff ν (A-B):ℝ):ℂ)*angularResidueNormTwist ℓ q η t ν =
    ((MvPowerSeries.coeff ν A:ℝ):ℂ)*angularResidueNormTwist ℓ q η t ν -
      ((MvPowerSeries.coeff ν B:ℝ):ℂ)*angularResidueNormTwist ℓ q η t ν
  rw [map_sub,Complex.ofReal_sub,sub_mul]

lemma angularTwistArithmetic_coeff_primary (q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (hu : AngularUnitCompatible q η ℓ)
    (t : ℝ) (A : EisensteinArithmeticFunction) {n : Eisenstein} (hn : primary n) :
    MvPowerSeries.coeff (idealExponentOf n) (angularTwistArithmetic ℓ q η t A) =
      ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*
        η (Ideal.Quotient.mk (modulus q) n)*theta ℓ n*mellinPhase t (norm n) := by
  change ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*
    (angularResidueIdealChar q η ℓ (idealExponentOf n)*mellinPhase t (idealExponentNorm (idealExponentOf n))) = _
  rw [angularResidueIdealChar_primaryNormalize η hu,idealPrimaryGenerator_at_element hn,
    idealExponentOf_norm (primary_ne_zero hn)]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma shortArithmeticFactor_norm {F X : ℝ} {A : EisensteinArithmeticFunction}
    (hA : ShortArithmeticFactor F A) (hX : 1 ≤ X) {a : Eisenstein}
    (ha : a ∈ primaryElementBall X) :
    ‖((MvPowerSeries.coeff (idealExponentOf a) A : ℝ) : ℂ)‖ ≤ 1+Real.log X := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  obtain ⟨ha,hNa⟩ := mem_primaryElementBall.mp ha
  rcases hA with rfl | rfl | rfl
  · rw [Complex.norm_real,Real.norm_eq_abs]
    exact (shortIdealMoebius_abs_le_one F _).trans (by linarith)
  · simp only [MvPowerSeries.coeff_apply,idealZeta,Complex.ofReal_one,norm_one]
    linarith
  · rw [MvPowerSeries.coeff_apply,idealLogNorm,idealExponentOf_norm (primary_ne_zero ha),
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (one_le_norm (primary_ne_zero ha)))]
    have h := Real.log_le_log (norm_pos_of_ne_zero (primary_ne_zero ha)) hNa
    linarith

lemma shortArithmeticFactor_twisted_norm {F X : ℝ} {A : EisensteinArithmeticFunction}
    (hA : ShortArithmeticFactor F A) (hX : 1 ≤ X) {a : Eisenstein}
    (ha : a ∈ primaryElementBall X) (u : ℂ) (hu : ‖u‖ ≤ 1) :
    ‖((MvPowerSeries.coeff (idealExponentOf a) A : ℝ) : ℂ)*u‖ ≤ 1+Real.log X := by
  rw [norm_mul]
  exact (mul_le_of_le_one_right (_root_.norm_nonneg _) hu).trans
    (shortArithmeticFactor_norm hA hX ha)

lemma primaryElementBall_card_le {X : ℝ} (hX : 0 ≤ X) :
    ((primaryElementBall X).card : ℝ) ≤ 18*X :=
  (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (nonzeroNormBall_card_le hX)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogSmoothWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic full factors are exact linear combinations of two smooth
weights. No logarithmic coefficient is silently discarded. -/
noncomputable section
open Set Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_weighted_smooth_finite (c : Eisenstein → ℂ) (W : ℝ → ℂ)
    {B Z : ℝ} (hZ : 0 < Z) (hW : ∀ x : ℝ, B < x → W x = 0) :
    (∑' a : Eisenstein, if primary a then c a*W (norm a/Z) else 0) =
      ∑ a ∈ primaryElementBall (B*Z), c a*W (norm a/Z) := by
  calc
    _ = ∑ a ∈ primaryElementBall (B*Z), if primary a then c a*W (norm a/Z) else 0 := by
      apply tsum_eq_sum
      intro a ha
      by_cases hprim : primary a
      · have hN : B*Z < norm a := lt_of_not_ge (fun h => ha (mem_primaryElementBall.mpr ⟨hprim,h⟩))
        rw [ite_eq_left hprim,hW _ ((lt_div_iff₀ hZ).mpr hN),mul_zero]
      · rw [ite_eq_right hprim]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [ite_eq_left (mem_primaryElementBall.mp ha).1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularFullSmoothFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact classification of the full smooth factors from the short inverse.
The short Möbius alternative vanishes once the dyad lies above its support. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryAngularShortSmoothSum_eq_polynomial (ℓ : ℤ) (A : EisensteinArithmeticFunction)
    (a b q : Eisenstein) (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ)
    {B Z : ℝ} (hZ : 0 < Z) (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    primaryAngularShortSmoothSum ℓ A a b q η W Z t =
      primaryIdealPolynomial (B*Z) A (fun x =>
        mixedCubic a b x*η (Ideal.Quotient.mk (modulus q) x)*theta ℓ x*mellinPhase t (norm x)*W (norm x/Z)) := by
  rw [primaryIdealPolynomial_eq_elements]
  unfold primaryAngularShortSmoothSum
  rw [primary_weighted_smooth_finite _ W hZ hW]
  apply Finset.sum_congr rfl
  intro x _
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorbing the explicit logarithmic factors in the short-polynomial
moments, without making subpower growth an assumption. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma one_add_log_small_power {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 1 ≤ x → 1+Real.log x ≤ A*x^η := by
  refine ⟨1+1/η,by positivity,?_⟩
  intro x hx
  have hp := Real.one_le_rpow hx hη.le
  have hl := Real.log_le_rpow_div (zero_le_one.trans hx) hη
  calc
    _ ≤ x^η+x^η/η := add_le_add hp hl
    _ = _ := by ring

lemma shortFactorPolynomial_norm_le {F X : ℝ} {A : EisensteinArithmeticFunction}
    (hA : ShortArithmeticFactor F A) (hX : 1 ≤ X) (u : Eisenstein → ℂ)
    (hu : ∀ a ∈ primaryElementBall X, ‖u a‖ ≤ 1) :
    ‖primaryIdealPolynomial X A u‖ ≤ 18*X*(1+Real.log X) := by
  rw [primaryIdealPolynomial_eq_elements]
  calc
    _ ≤ ∑ a ∈ primaryElementBall X,
        ‖((MvPowerSeries.coeff (idealExponentOf a) A:ℝ):ℂ)*u a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ primaryElementBall X, (1+Real.log X) :=
      Finset.sum_le_sum (fun a ha => shortArithmeticFactor_twisted_norm hA hX ha _ (hu a ha))
    _ = ((primaryElementBall X).card:ℝ)*(1+Real.log X) := by
      rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (primaryElementBall_card_le (by linarith))
      (by linarith [Real.log_nonneg hX])

theorem shortFactorPolynomial_norm_small_power {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F X : ℝ) (A : EisensteinArithmeticFunction),
      ShortArithmeticFactor F A → 1 ≤ X → ∀ u : Eisenstein → ℂ,
      (∀ a ∈ primaryElementBall X, ‖u a‖ ≤ 1) →
      ‖primaryIdealPolynomial X A u‖ ≤ C*X^(1+η) := by
  obtain ⟨C,hC,hbound⟩ := one_add_log_small_power hη
  refine ⟨18*C,by positivity,?_⟩
  intro F X A hA hX u hu
  apply (shortFactorPolynomial_norm_le hA hX u hu).trans
  calc
    _ ≤ 18*X*(C*X^η) := mul_le_mul_of_nonneg_left (hbound X hX) (by positivity)
    _ = (18*C)*X^(1+η) := by
      rw [Real.rpow_add (zero_lt_one.trans_le hX),Real.rpow_one]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmoothShortFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructing the actual smooth short-factor family used in the exceptional
moments. Finite characters, norm phases and smooth dyads are explicit. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angularShortFamily_mixedValue {ι : Type*} (ℓ : ℤ) (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hq : ∀ i, q i ≠ 0) (hW : ∀ i x, ‖W i x‖ ≤ 1)
    (hcut : ∀ i x, 2 < x → W i x = 0) (j : ℕ) (i : ι) (p : Eisenstein × Eisenstein) :
    (angularShortFamilyOfSmoothWeights ℓ F X A q η W t hA hX hq hW).mixedValue j i p =
      primaryAngularShortSmoothSum ℓ (A i) p.1 p.2 (q i) (η i) (W i) (X i/2) (t i) := by
  rw [primaryAngularShortSmoothSum_eq_polynomial ℓ (A i) p.1 p.2 (q i) (η i) (W i)
    (by linarith [hX i] : 0 < X i/2) (hcut i)]
  have hx : 2*(X i/2) = X i := by ring
  rw [hx]
  unfold ShortFactorFamily.mixedValue
  change primaryIdealPolynomial (X i) (A i) (fun n =>
    smoothAngularShortTwist ℓ (η i) (W i) (X i) (t i) n*mixedCubic p.1 p.2 n) = _
  congr 1
  funext n
  unfold smoothAngularShortTwist smoothShortTwist
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_AllShortNeighborhoods
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conductor-neighborhood savings for the literal short factors,
with cardinality and amplitude bounds derived from their finite supports. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma neighborhood_balanced_card (S : Finset (Eisenstein × Eisenstein))
    {Y L : ℝ} (hY : 324 ≤ Y) (hL : 0 ≤ L) (hLY : L ≤ Y)
    (hS : ∀ p ∈ S, PrimarySquarefreePair p ∧ norm p.1 ≤ L ∧ norm p.2 ≤ L) :
    (S.card:ℝ) ≤ Y^4 := by
  have hc := balanced_pair_card S hL
    (fun p hp => ⟨(hS p hp).1.1,(hS p hp).1.2.1,(hS p hp).2⟩)
  calc
    _ ≤ 324*L^2 := hc
    _ ≤ 324*Y^2 := by gcongr
    _ ≤ Y^2*Y^2 := by gcongr; nlinarith
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteMellinProduct
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma nonnegative_product_cpow {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (hN : ∀ i ∈ S, 0 ≤ N i) (s : ℂ) :
    ((∏ i ∈ S, N i : ℝ):ℂ)^s = ∏ i ∈ S, (N i:ℂ)^s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hN i (Finset.mem_insert_self i S))
        (Finset.prod_nonneg (fun j hj => hN j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hN j (Finset.mem_insert_of_mem hj)),Finset.prod_insert hi]

theorem smooth_mellin_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (a : (i : ι) → κ i → ℂ) (N : (i : ι) → κ i → ℝ)
    (hN : ∀ i x, 0 < N i x)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (σ : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    (∑ x : (i : ι) → κ i, (∏ i, a i (x i))*W ((∏ i, N i (x i))/Z)) =
      ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin W (σ+(τ:ℂ)*Complex.I)*(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*
          ∏ i, (∑ x : κ i, a i x*(N i x:ℂ)^(-(σ+(τ:ℂ)*Complex.I))) := by
  rw [smooth_mellin_finite (fun x : (i : ι) → κ i => ∏ i, a i (x i))
    (fun x => ∏ i, N i (x i)) (fun x => Finset.prod_pos (fun i _ => hN i (x i)))
    W hW hpos hsm σ hZ]
  congr 1
  apply integral_congr_ae
  filter_upwards with τ
  congr 1
  rw [Fintype.prod_sum (fun (i : ι) (x : κ i) =>
    a i x*(N i x:ℂ)^(-(σ+(τ:ℂ)*Complex.I)))]
  apply Finset.sum_congr rfl
  intro x _
  rw [nonnegative_product_cpow _ _ (fun i _ => (hN i (x i)).le),Finset.prod_mul_distrib]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortTupleMellin
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin separation for the actual smooth short-inverse factors. The
integrand is a product of the original primary sums, with a common shift. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mellinPhase_mul_neg_cpow {x : ℝ} (hx : 0 < x) (t τ : ℝ) :
    mellinPhase t x*(x:ℂ)^(-((τ:ℂ)*Complex.I)) = mellinPhase (t-τ) x := by
  rw [show -((τ:ℂ)*Complex.I) = ((-τ:ℝ):ℂ)*Complex.I by push_cast; ring,
    ← mellinPhase_eq_cpow hx]
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularShortTupleMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin separation for the actual smooth short-inverse factors. The
integrand is a product of the original primary sums, with a common shift. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryAngularShortSmoothSum_eq_subtype (ℓ : ℤ) (A : EisensteinArithmeticFunction)
    (a b q : Eisenstein) (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ)
    {X : ℝ} (hX : 0 < X) (hW : ∀ x : ℝ, 2 < x → W x = 0) (t : ℝ) :
    primaryAngularShortSmoothSum ℓ A a b q η W (X/2) t =
      ∑ n : primaryElementBall X,
        ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*
          (mixedCubic a b n*η (Ideal.Quotient.mk (modulus q) n)*theta ℓ n*mellinPhase t (norm n))*
            W (norm n/(X/2)) := by
  rw [primaryAngularShortSmoothSum_eq_polynomial ℓ A a b q η W (by linarith : 0 < X/2) hW,
    show 2*(X/2) = X by ring,primaryIdealPolynomial_eq_elements]
  symm
  change (∑ n ∈ (primaryElementBall X).attach, _) = _
  rw [Finset.sum_attach (f := fun n : Eisenstein =>
    ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*
      (mixedCubic a b n*η (Ideal.Quotient.mk (modulus q) n)*theta ℓ n*mellinPhase t (norm n))*
        W (norm n/(X/2)))]
  apply Finset.sum_congr rfl
  intro n _
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primaryAngularShortTupleSum_mellin (ℓ : ℤ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hW : ∀ i x, 2 < x → W i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ V) {Z : ℝ} (hZ : 0 < Z) :
    primaryAngularShortTupleSum ℓ X A a b q η W t V Z =
      ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin V ((τ:ℂ)*Complex.I)*(Z:ℂ)^((τ:ℂ)*Complex.I)*
          ∏ i, primaryAngularShortSmoothSum ℓ (A i) a b (q i) (η i) (W i) (X i/2) (t i-τ) := by
  unfold primaryAngularShortTupleSum
  rw [smooth_mellin_product
    (fun i (n : primaryElementBall (X i)) =>
      ((MvPowerSeries.coeff (idealExponentOf n) (A i):ℝ):ℂ)*
        (mixedCubic a b n*η i (Ideal.Quotient.mk (modulus (q i)) n)*theta ℓ n*
          mellinPhase (t i) (norm n))*W i (norm n/(X i/2)))
    (fun i (n : primaryElementBall (X i)) => norm n)
    (fun i n => norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp n.property).1))
    V hV hpos hsm 0 hZ]
  simp only [Complex.ofReal_zero,zero_add]
  congr 1
  apply integral_congr_ae
  filter_upwards with τ
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [primaryAngularShortSmoothSum_eq_subtype ℓ (A i) a b (q i) (η i) (W i) (hX i) (hW i)]
  apply Finset.sum_congr rfl
  intro n _
  have hn : 0 < norm (n:Eisenstein) :=
    norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp n.property).1)
  rw [← mellinPhase_mul_neg_cpow hn]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinMomentTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing an actual uniform finite-row moment through an integrable Mellin
weight. The proof is the triangle inequality in the finite Euclidean space. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem finite_row_integral_moment {Ω κ : Type*} [MeasurableSpace Ω]
    [Fintype κ] {μ : Measure Ω} (f : κ → Ω → ℂ) (w : Ω → ℂ)
    (hf : AEStronglyMeasurable (fun t => WithLp.toLp 2 (fun r => f r t)) μ)
    (hw : Integrable w μ) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ᵐ t ∂μ, (∑ r, ‖f r t‖^2) ≤ B) :
    (∑ r, ‖∫ t, w t*f r t ∂μ‖^2) ≤ (∫ t, ‖w t‖ ∂μ)^2*B := by
  let F : Ω → EuclideanSpace ℂ κ := fun t => WithLp.toLp 2 (fun r => f r t)
  let G : Ω → EuclideanSpace ℂ κ := fun t => w t • F t
  have hFn : ∀ᵐ t ∂μ, ‖F t‖ ≤ Real.sqrt B := by
    filter_upwards [hb] with t ht
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_sqrt ht
  have hGn : ∀ᵐ t ∂μ, ‖G t‖ ≤ ‖w t‖*Real.sqrt B := by
    filter_upwards [hFn] with t ht
    dsimp [G]
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ht (_root_.norm_nonneg _)
  have hG : Integrable G μ := (hw.norm.mul_const (Real.sqrt B)).mono'
    (hw.aestronglyMeasurable.smul hf) hGn
  have hcoord (r : κ) : (∫ t, G t ∂μ) r = ∫ t, w t*f r t ∂μ := by
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : κ => ℂ) r).integral_comp_comm hG).symm
  have hbound : ‖∫ t, G t ∂μ‖ ≤ (∫ t, ‖w t‖ ∂μ)*Real.sqrt B := by
    apply (norm_integral_le_integral_norm G).trans
    rw [← integral_mul_const]
    exact integral_mono_ae hG.norm (hw.norm.mul_const _) hGn
  calc
    _ = ‖∫ t, G t ∂μ‖^2 := by rw [EuclideanSpace.norm_sq_eq]; simp_rw [hcoord]
    _ ≤ ((∫ t, ‖w t‖ ∂μ)*Real.sqrt B)^2 :=
      pow_le_pow_left₀ (_root_.norm_nonneg _) hbound 2
    _ = _ := by rw [mul_pow,Real.sq_sqrt hB]

theorem finite_interval_integral_moment {κ : Type*} [Fintype κ]
    (f : κ → ℝ → ℂ) (hf : ∀ r, Continuous (f r)) (w : ℝ → ℂ)
    (hw : Integrable w) (T B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ t ∈ Set.Icc (-T) T, (∑ r, ‖f r t‖^2) ≤ B) :
    (∑ r, ‖∫ t in Set.Icc (-T) T, w t*f r t‖^2) ≤
      (∫ t, ‖w t‖)^2*B := by
  have hc : Continuous (fun t => WithLp.toLp 2 (fun r => f r t)) :=
    (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp (continuous_pi hf)
  have ha : ∀ᵐ t ∂(volume.restrict (Set.Icc (-T) T)), (∑ r, ‖f r t‖^2) ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hb t ht
  have h := finite_row_integral_moment f w hc.aestronglyMeasurable hw.restrict hB ha
  apply h.trans
  have hm : (∫ t in Set.Icc (-T) T, ‖w t‖) ≤ ∫ t, ‖w t‖ :=
    setIntegral_le_integral hw.norm (Filter.Eventually.of_forall (fun _ => _root_.norm_nonneg _))
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (integral_nonneg (fun _ => _root_.norm_nonneg _)) hm 2) hB

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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmoothShortContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem continuous_primaryAngularShortSmoothSum (ℓ : ℤ) (A : EisensteinArithmeticFunction)
    (a b q : Eisenstein) (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ)
    {X : ℝ} (hX : 0 < X) (hW : ∀ x : ℝ, 2 < x → W x = 0) :
    Continuous (primaryAngularShortSmoothSum ℓ A a b q η W (X/2)) := by
  have he := funext (primaryAngularShortSmoothSum_eq_subtype ℓ A a b q η W hX hW)
  rw [he]
  apply continuous_finsetSum
  intro n _
  unfold mellinPhase
  fun_prop

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

lemma normPartitionWeight_telescope (x : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, normPartitionWeight (x/(4/3:ℝ)^k)) =
      (normPartitionStep x - normPartitionStep (x/(4/3:ℝ)^N) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,normPartitionWeight]
    have he : 3*(x/(4/3:ℝ)^N)/4 = x/(4/3:ℝ)^(N+1) := by
      rw [pow_succ]
      ring
    rw [he]
    push_cast
    ring

theorem normPartitionWeight_partition {B x : ℝ} {N : ℕ}
    (hx : 1 ≤ x) (hB : x ≤ B) (hN : 2*B ≤ (4/3:ℝ)^N) :
    (∑ k ∈ Finset.range N, normPartitionWeight (2*x/(4/3:ℝ)^k)) = 1 := by
  rw [normPartitionWeight_telescope,
    normPartitionStep_one (show 4/3 ≤ 2*x by linarith)]
  have hpow : 0 < (4/3:ℝ)^N := pow_pos (by norm_num) _
  rw [normPartitionStep_zero ((div_le_one hpow).mpr (by linarith))]
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TruncatedProductMoment
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The central Mellin integral inherits the proved exceptional product
moment, with a constant independent of the outer norm scale. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eventual_shifted_height_bound :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ t τ : ℝ,
      |t| ≤ Y^(361/1000:ℝ) → |τ| ≤ Y^(9/25:ℝ) → |t-τ| ≤ Y^(37/100:ℝ) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 9/1000 by norm_num)).eventually_ge_atTop (2:ℝ))
  refine ⟨max 1 T,?_⟩
  intro Y hY t τ ht hτ
  have hYp : 0 < Y := zero_lt_one.trans_le ((le_max_left _ _).trans hY)
  have hτ' : |τ| ≤ Y^(361/1000:ℝ) := hτ.trans
    (Real.rpow_le_rpow_of_exponent_le ((le_max_left _ _).trans hY) (by norm_num))
  calc
    _ ≤ |t|+|τ| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le t 0 τ
    _ ≤ 2*Y^(361/1000:ℝ) := by linarith
    _ ≤ Y^(9/1000:ℝ)*Y^(361/1000:ℝ) :=
      mul_le_mul_of_nonneg_right (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularBalancedTruncatedNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Central Mellin transfer preserving the proved conductor neighborhood. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_balanced_truncated_neighborhood_moment (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {D : ℝ} (hD : 0 < D) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein))
      (V : ℝ → ℂ) (Z : ℝ),
      Y₀ ≤ Y → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
      (∀ i, q i ≠ 0) → (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) → HasCompactSupport V → tsupport V ⊆ Ioi 0 →
      ContDiff ℝ ∞ V → 0 < Z →
      (∑ a : P, ‖∫ τ in Icc (-(Y^(9/25:ℝ))) (Y^(9/25:ℝ)),
        zeroLineMellinWeight V Z τ*
          ∏ i, primaryAngularShortSmoothSum ℓ (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight (X i/2) (t i-τ)‖^2) ≤
        (zeroLineMellinMass V)^2*Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hbound⟩ := angular_balanced_smooth_product_neighborhood hpub ℓ hHuxley
    (fun _ : ι => normPartitionWeight) (fun _ => normPartitionWeight_compact)
    (fun _ => normPartitionWeight_positive_support) (fun _ => normPartitionWeight_smooth)
    (fun _ _ hx => normPartitionWeight_low hx) (fun _ _ hx => normPartitionWeight_high hx)
    (fun _ => normPartitionWeight_norm) hGI hGQ hD
  obtain ⟨T₁,hheight⟩ := eventual_shifted_height_bound
  refine ⟨κ,hκ,hκhi,ε,hε,max 1 (max T T₁),?_⟩
  intro F Y X A q η t P V Z hY hF hA hX hlo hhi hq hη hqY ht hP hV hpos hsm hZ
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYT : T ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans hY)
  let f : P → ℝ → ℂ := fun a τ =>
    ∏ i, primaryAngularShortSmoothSum ℓ (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight (X i/2) (t i-τ)
  have hf (a : P) : Continuous (f a) := by
    apply continuous_finsetProd
    intro i _
    exact (continuous_primaryAngularShortSmoothSum ℓ (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight
      (by linarith [hX i]) (fun _ hx => normPartitionWeight_high hx)).comp
        (continuous_const.sub continuous_id)
  have hb (τ : ℝ) (hτ : τ ∈ Icc (-(Y^(9/25:ℝ))) (Y^(9/25:ℝ))) :
      (∑ a : P, ‖f a τ‖^2) ≤ Y^(7/3-ε) := by
    have hτabs : |τ| ≤ Y^(9/25:ℝ) := abs_le.mpr hτ
    have hm := hbound F Y X A q η (fun i => t i-τ) P hYT hF hA hX hlo hhi hq hη hqY
      (fun i => hheight Y hYT₁ (t i) τ (ht i) hτabs) hP
    change (∑ a ∈ P.attach, ‖f a τ‖^2) ≤ _
    dsimp only [f]
    rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
      ‖∏ i, primaryAngularShortSmoothSum ℓ (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i)
        normPartitionWeight (X i/2) (t i-τ)‖^2)]
    exact hm
  have hm := finite_interval_integral_moment f hf (zeroLineMellinWeight V Z)
    (zeroLineMellinWeight_integrable V hV hpos hsm hZ) (Y^(9/25:ℝ))
    (Y^(7/3-ε)) (Real.rpow_nonneg (zero_le_one.trans hY1) _) hb
  rwa [zeroLineMellinWeight_mass V hZ] at hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortProductSize
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform trivial product bound used only to control Mellin tails. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem short_family_product_size :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ShortFactorFamily ι) (j : ℕ) (a b : Eisenstein),
      primary a → primary b →
      ‖∏ i, F.mixedValue j i (a,b)‖ ≤ C*(∏ i, F.length j i)^2 := by
  obtain ⟨K,hK,hbound⟩ := shortFactorPolynomial_norm_small_power (show (0:ℝ) < 1 by norm_num)
  refine ⟨K^(Fintype.card ι),pow_pos hK _,?_⟩
  intro F j a b ha hb
  have hi (i : ι) : ‖F.mixedValue j i (a,b)‖ ≤ K*(F.length j i)^2 := by
    have h := hbound (F.cutoff j) (F.length j i) (F.coefficient j i)
      (F.factor_spec j i) (F.length_ge_one j i)
      (fun n => F.twist j i n*mixedCubic a b n) (by
        intro n hn
        rw [norm_mul]
        exact (mul_le_mul (F.twist_bound j i n hn) (norm_mixedCubic_le_one ha hb n)
          (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
    simpa only [ShortFactorFamily.mixedValue,show (1+(1:ℝ)) = 2 by norm_num,
      Real.rpow_two] using h
  calc
    _ = ∏ i, ‖F.mixedValue j i (a,b)‖ := norm_prod _ _
    _ ≤ ∏ i, K*(F.length j i)^2 := Finset.prod_le_prod
      (fun _ _ => _root_.norm_nonneg _) (fun i _ => hi i)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.prod_pow,Finset.card_univ]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularShortProductSize
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform size bound for angular short products, used for Mellin tails. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem angular_smooth_short_product_size (ℓ : ℤ) {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ)
      (t : ι → ℝ) (a b : Eisenstein),
      (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, q i ≠ 0) → (∀ i x, ‖W i x‖ ≤ 1) → (∀ i x, 2 < x → W i x = 0) →
      (∏ i, X i) ≤ D*Y → primary a → primary b →
      ‖∏ i, primaryAngularShortSmoothSum ℓ (A i) a b (q i) (η i) (W i) (X i/2) (t i)‖ ≤ C*Y^2 := by
  obtain ⟨C,hC,hbound⟩ := short_family_product_size (ι := ι)
  refine ⟨C*D^2,mul_pos hC (sq_pos_of_pos hD),?_⟩
  intro F Y X A q η W t a b hA hX hq hW hcut hprod ha hb
  let K := angularShortFamilyOfSmoothWeights ℓ F X A q η W t hA hX hq hW
  have h := hbound K 0 a b ha hb
  simp only [K,angularShortFamily_mixedValue ℓ F X A q η W t hA hX hq hW hcut] at h
  apply h.trans
  have hp := pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hX i))) hprod 2
  calc
    _ ≤ C*(D*Y)^2 := mul_le_mul_of_nonneg_left hp hC.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularWeightedTupleMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full Mellin separation of the angular short tuple. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primaryAngularShortTupleSum_integral (ℓ : ℤ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hW : ∀ i x, 2 < x → W i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) {Z : ℝ} (hZ : 0 < Z) :
    primaryAngularShortTupleSum ℓ X A a b q η W t V Z =
      ∫ τ : ℝ, zeroLineMellinWeight V Z τ*
        ∏ i, primaryAngularShortSmoothSum ℓ (A i) a b (q i) (η i) (W i) (X i/2) (t i-τ) := by
  rw [primaryAngularShortTupleSum_mellin ℓ X A a b q η W t hX hW V hV hpos hsm hZ,
    ← integral_const_mul]
  congr 1
  funext τ
  unfold zeroLineMellinWeight
  ring

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

lemma outside_interval_abs {T t : ℝ} (ht : t ∈ (Icc (-T) T)ᶜ) : T ≤ |t| := by
  by_contra h
  have ha : |t| < T := lt_of_not_ge h
  exact ht ⟨by linarith [neg_abs_le t],by linarith [le_abs_self t]⟩

lemma weighted_height_tail (w : ℝ → ℂ) (hw : Integrable w) (A : ℕ)
    (hA : Integrable (fun t : ℝ => |t|^A*‖w t‖)) {T : ℝ} (hT : 0 < T) :
    (∫ t in (Icc (-T) T)ᶜ, ‖w t‖) ≤
      (∫ t : ℝ, |t|^A*‖w t‖)/T^A := by
  apply (le_div_iff₀ (pow_pos hT A)).mpr
  rw [mul_comm,← integral_const_mul]
  apply (integral_mono_ae (hw.norm.restrict.const_mul _) hA.restrict ?_).trans
    (setIntegral_le_integral hA (Filter.Eventually.of_forall (fun _ => by positivity)))
  filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hT.le (outside_interval_abs ht) A) (_root_.norm_nonneg _)

lemma bounded_product_height_tail (w f : ℝ → ℂ) (hw : Integrable w) (A : ℕ)
    (hA : Integrable (fun t : ℝ => |t|^A*‖w t‖)) {T B : ℝ}
    (hT : 0 < T) (hB : 0 ≤ B) (hf : ∀ t, ‖f t‖ ≤ B) :
    ‖∫ t in (Icc (-T) T)ᶜ, w t*f t‖ ≤
      (B/T^A)*(∫ t : ℝ, |t|^A*‖w t‖) := by
  have hn : ‖∫ t in (Icc (-T) T)ᶜ, w t*f t‖ ≤
      B*(∫ t in (Icc (-T) T)ᶜ, ‖w t‖) := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hw.norm.restrict.const_mul B)
    filter_upwards with t
    rw [norm_mul,mul_comm B]
    exact mul_le_mul_of_nonneg_left (hf t) (_root_.norm_nonneg _)
  calc
    _ ≤ B*(∫ t in (Icc (-T) T)ᶜ, ‖w t‖) := hn
    _ ≤ B*((∫ t : ℝ, |t|^A*‖w t‖)/T^A) :=
      mul_le_mul_of_nonneg_left (weighted_height_tail w hw A hA hT) hB
    _ = _ := by ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullMellinMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joining the central Mellin moment to a proved rapid tail bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma norm_square_le_central_tail (x y : ℂ) {H : ℝ} (h : ‖x-y‖ ≤ H) :
    ‖x‖^2 ≤ 2*‖y‖^2+2*H^2 := by
  have hx : ‖x‖ ≤ ‖y‖+H := by
    calc
      _ = ‖y+(x-y)‖ := by congr 1; ring
      _ ≤ ‖y‖+‖x-y‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl h
  have hH : 0 ≤ H := (_root_.norm_nonneg _).trans h
  have hsq := pow_le_pow_left₀ (_root_.norm_nonneg _) hx 2
  nlinarith [sq_nonneg (‖y‖-H),sq_nonneg ‖x‖]

theorem full_mellin_moment_of_central {κ : Type*} [Fintype κ]
    (f : κ → ℝ → ℂ) (hf : ∀ r, Continuous (f r)) (w : ℝ → ℂ)
    (hw : Integrable w) (A : ℕ) (hA : Integrable (fun t : ℝ => |t|^A*‖w t‖))
    {T L M : ℝ} (hT : 0 < T) (hL : 0 ≤ L) (hsize : ∀ r t, ‖f r t‖ ≤ L)
    (hcentral : (∑ r, ‖∫ t in Icc (-T) T, w t*f r t‖^2) ≤ M) :
    (∑ r, ‖∫ t, w t*f r t‖^2) ≤ 2*M+
      2*(Fintype.card κ:ℝ)*((L/T^A)*(∫ t : ℝ, |t|^A*‖w t‖))^2 := by
  let H := (L/T^A)*(∫ t : ℝ, |t|^A*‖w t‖)
  have happrox (r : κ) :
      ‖(∫ t, w t*f r t)-(∫ t in Icc (-T) T, w t*f r t)‖ ≤ H := by
    have hi : Integrable (fun t => w t*f r t) := (hw.norm.mul_const L).mono'
      (hw.aestronglyMeasurable.mul (hf r).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun t => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hsize r t) (_root_.norm_nonneg _)))
    rw [← integral_add_compl measurableSet_Icc hi,add_sub_cancel_left]
    exact bounded_product_height_tail w (f r) hw A hA hT hL (hsize r)
  calc
    _ ≤ ∑ r, (2*‖∫ t in Icc (-T) T, w t*f r t‖^2+2*H^2) :=
      Finset.sum_le_sum (fun r _ => norm_square_le_central_tail _ _ (happrox r))
    _ = 2*(∑ r, ‖∫ t in Icc (-T) T, w t*f r t‖^2)+2*(Fintype.card κ:ℝ)*H^2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _ ≤ _ := by dsimp [H]; nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinMomentPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed powers in the central-plus-tail short-convolution estimate. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem absorb_short_mellin_bounds {ε : ℝ} (hε : 0 < ε) (C E : ℝ)
    (hC : 0 ≤ C) (hE : 0 ≤ E) :
    ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      C*Y^(7/3-ε)+E*Y^(-42/5:ℝ) ≤ Y^(7/3-min ε (1/3)/2) := by
  let η := min ε (1/3:ℝ)
  have hη : 0 < η := lt_min hε (by norm_num)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < η/2 by linarith)).eventually_ge_atTop (C+E))
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y hY
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hηε : η ≤ ε := min_le_left _ _
  have hη3 : η ≤ 1/3 := min_le_right _ _
  calc
    _ ≤ C*Y^(7/3-η)+E*Y^(7/3-η) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)) hC
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)) hE
    _ = (C+E)*Y^(7/3-η) := by ring
    _ ≤ Y^(η/2)*Y^(7/3-η) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; dsimp [η]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NeighborhoodTailPower
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A thirtieth Mellin moment handles the larger row count uniformly across
both exceptional conductor neighborhoods. -/
noncomputable section
namespace CubicFirstMoment

lemma neighborhood_mellin_tail_power {Y K J : ℝ} (hY : 0 < Y) :
    2*Y^4*((K*Y^2/(Y^(9/25:ℝ))^30)*J)^2 =
      (2*K^2*J^2)*Y^(-68/5:ℝ) := by
  have hp : (Y^(9/25:ℝ))^30 = Y^(54/5:ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le]
    norm_num
  have hd : Y^2/Y^(54/5:ℝ) = Y^(-44/5:ℝ) := by
    rw [← Real.rpow_two,← Real.rpow_sub hY]
    norm_num
  rw [hp,show K*Y^2/Y^(54/5:ℝ) = K*(Y^2/Y^(54/5:ℝ)) by ring,hd]
  have he : Y^4*(Y^(-44/5:ℝ))^2 = Y^(-68/5:ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le,← Real.rpow_natCast,← Real.rpow_add hY]
    norm_num
  calc
    _ = (2*K^2*J^2)*(Y^4*(Y^(-44/5:ℝ))^2) := by ring
    _ = _ := by rw [he]

lemma neighborhood_mellin_tail_le {Y K J : ℝ} (hY : 1 ≤ Y) :
    2*Y^4*((K*Y^2/(Y^(9/25:ℝ))^30)*J)^2 ≤
      (2*K^2*J^2)*Y^(-42/5:ℝ) := by
  rw [neighborhood_mellin_tail_power (zero_lt_one.trans_le hY)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularBalancedWeightedNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full weighted short-tuple moments throughout the exceptional conductor
neighborhood, with an explicit thirtieth-moment tail. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_balanced_weighted_tuple_neighborhood (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|((ℓ:ℤ):ℝ)|/2) (2+|((ℓ:ℤ):ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|((ℓ:ℤ):ℝ)|/2) (1/2-(m:ℝ)))
    {D : ℝ} (hD : 0 < D) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)) (Z : ℝ),
      Y₀ ≤ Y → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
      (∀ i, q i ≠ 0) → (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) → 0 < Z →
      (∑ a ∈ P, ‖primaryAngularShortTupleSum ℓ X A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η
        (fun _ => normPartitionWeight) t V Z‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hcentral⟩ := angular_balanced_truncated_neighborhood_moment (ι := ι) hpub ℓ hHuxley hGI hGQ hD
  obtain ⟨K,hK,hsize⟩ := angular_smooth_short_product_size (ι := ι) ℓ hD
  let J : ℝ := (1/(2*Real.pi))*(∫ τ : ℝ, |τ|^30*‖mellin V ((τ:ℂ)*Complex.I)‖)
  obtain ⟨T₁,hT₁,habsorb⟩ := absorb_short_mellin_bounds hε
    (2*(zeroLineMellinMass V)^2) (2*K^2*J^2) (by positivity) (by positivity)
  refine ⟨κ,hκ,hκhi,min ε (1/3)/2,div_pos (lt_min hε (by norm_num)) (by norm_num),
    max 324 (max T T₁),?_⟩
  intro F Y X A q η t P Z hY hF hA hX hlo hhi hq hη hqY ht hP hZ
  have hY324 : 324 ≤ Y := (le_max_left _ _).trans hY
  have hY0 : 0 < Y := by linarith
  have hYT : T ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans hY)
  let f : P → ℝ → ℂ := fun a τ =>
    ∏ i, primaryAngularShortSmoothSum ℓ (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight (X i/2) (t i-τ)
  have hf (a : P) : Continuous (f a) := by
    apply continuous_finsetProd
    intro i _
    exact (continuous_primaryAngularShortSmoothSum ℓ (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight
      (by linarith [hX i]) (fun _ hx => normPartitionWeight_high hx)).comp
        (continuous_const.sub continuous_id)
  have hs (a : P) (τ : ℝ) : ‖f a τ‖ ≤ K*Y^2 := by
    exact hsize F Y X A q η (fun _ => normPartitionWeight) (fun i => t i-τ) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2
      hA hX hq (fun _ => normPartitionWeight_norm)
      (fun _ _ hx => normPartitionWeight_high hx) hhi (hP a a.property).1.1 (hP a a.property).1.2.1
  have hc := hcentral F Y X A q η t P V Z hYT hF hA hX hlo hhi hq hη hqY ht hP hV hpos hsm hZ
  have hm := full_mellin_moment_of_central f hf (zeroLineMellinWeight V Z)
    (zeroLineMellinWeight_integrable V hV hpos hsm hZ) 30
    (zeroLineMellinWeight_moment_integrable V hV hpos hsm hZ 30)
    (Real.rpow_pos_of_pos hY0 _) (mul_nonneg hK.le (sq_nonneg Y)) hs hc
  rw [zeroLineMellinWeight_moment V hZ 30] at hm
  have hY1 : 1 ≤ Y := by linarith
  have hLY : Y^(1/3+κ) ≤ Y := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY1
      (by linarith : 1/3+κ ≤ 1)
  have hcard : (Fintype.card P:ℝ) ≤ Y^4 := by
    simpa only [Fintype.card_coe] using neighborhood_balanced_card P hY324
      (Real.rpow_nonneg hY0.le _) hLY
      (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.1⟩)
  have he (a : Eisenstein × Eisenstein) : primaryAngularShortTupleSum ℓ X A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η
      (fun _ => normPartitionWeight) t V Z = ∫ τ, zeroLineMellinWeight V Z τ*
        ∏ i, primaryAngularShortSmoothSum ℓ (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight (X i/2) (t i-τ) :=
    primaryAngularShortTupleSum_integral ℓ X A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η (fun _ => normPartitionWeight) t
      (fun i => by linarith [hX i]) (fun _ _ hx => normPartitionWeight_high hx) V hV hpos hsm hZ
  apply le_trans _ (habsorb Y hYT₁)
  calc
    _ = ∑ a : P, ‖∫ τ, zeroLineMellinWeight V Z τ*f a τ‖^2 := by
      simp_rw [he]
      symm
      change (∑ a ∈ P.attach, _) = _
      exact Finset.sum_attach P (fun a =>
        ‖∫ τ, zeroLineMellinWeight V Z τ*∏ i,
          primaryAngularShortSmoothSum ℓ (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight (X i/2) (t i-τ)‖^2)
    _ ≤ 2*((zeroLineMellinMass V)^2*Y^(7/3-ε))+
        2*(Fintype.card P:ℝ)*((K*Y^2/(Y^(9/25:ℝ))^30)*J)^2 := hm
    _ ≤ 2*((zeroLineMellinMass V)^2*Y^(7/3-ε))+
        2*Y^4*((K*Y^2/(Y^(9/25:ℝ))^30)*J)^2 := by gcongr
    _ ≤ (2*(zeroLineMellinMass V)^2)*Y^(7/3-ε)+(2*K^2*J^2)*Y^(-42/5:ℝ) := by
      simpa only [mul_assoc] using add_le_add
        (le_refl (2*((zeroLineMellinMass V)^2*Y^(7/3-ε))))
        (neighborhood_mellin_tail_le (K := K) (J := J) hY1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortTupleScales
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonzero smooth convolution piece automatically has comparable total
length. Thus the moment hypotheses need not be imposed on empty pieces. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma normPartitionWeight_nonzero_length {x X : ℝ} (hX : 0 < X)
    (h : normPartitionWeight (x/(X/2)) ≠ 0) : x ≤ X ∧ X ≤ 2*x := by
  have hp : 0 < X/2 := by linarith
  have hlo : 1 ≤ x/(X/2) := by
    by_contra hn
    exact h (normPartitionWeight_low (lt_of_not_ge hn))
  have hhi : x/(X/2) ≤ 2 := by
    by_contra hn
    exact h (normPartitionWeight_high (lt_of_not_ge hn))
  have h₁ := (le_div_iff₀ hp).mp hlo
  have h₂ := (div_le_iff₀ hp).mp hhi
  constructor <;> linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularShortTupleScales
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonzero smooth convolution piece automatically has comparable total
length. Thus the moment hypotheses need not be imposed on empty pieces. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primaryAngularShortTupleSum_nonzero_scales (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hX : ∀ i, 0 < X i) (hZ : 0 < Z)
    (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (h : primaryAngularShortTupleSum ℓ X A a b q η (fun _ => normPartitionWeight) t V Z ≠ 0) :
    Z ≤ ∏ i, X i ∧ (∏ i, X i) ≤ (2:ℝ)^(Fintype.card ι+1)*Z := by
  unfold primaryAngularShortTupleSum at h
  obtain ⟨n,_,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hp := (mul_ne_zero_iff.mp hn).1
  have hv := (mul_ne_zero_iff.mp hn).2
  have hi (i : ι) : norm (n i:Eisenstein) ≤ X i ∧ X i ≤ 2*norm (n i:Eisenstein) := by
    apply normPartitionWeight_nonzero_length (hX i)
    exact (mul_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i))).2
  have hlo : 1 ≤ (∏ i, norm (n i:Eisenstein))/Z := by
    by_contra hlt
    exact hv (hVlo _ (lt_of_not_ge hlt))
  have hhi : (∏ i, norm (n i:Eisenstein))/Z ≤ 2 := by
    by_contra hgt
    exact hv (hVhi _ (lt_of_not_ge hgt))
  constructor
  · simpa only [one_mul] using ((le_div_iff₀ hZ).mp hlo).trans
      (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (hi i).1))
  · calc
      _ ≤ ∏ i, 2*norm (n i:Eisenstein) := Finset.prod_le_prod
        (fun i _ => (hX i).le) (fun i _ => (hi i).2)
      _ = (2:ℝ)^(Fintype.card ι)*(∏ i, norm (n i:Eisenstein)) := by
        rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
      _ ≤ (2:ℝ)^(Fintype.card ι)*(2*Z) :=
        mul_le_mul_of_nonneg_left ((div_le_iff₀ hZ).mp hhi) (by positivity)
      _ = _ := by rw [pow_succ]; ring

theorem primaryAngularShortTupleSum_zero_outside_scales (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hX : ∀ i, 0 < X i) (hZ : 0 < Z)
    (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hscale : ¬(Z ≤ ∏ i, X i ∧ (∏ i, X i) ≤ (2:ℝ)^(Fintype.card ι+1)*Z)) :
    primaryAngularShortTupleSum ℓ X A a b q η (fun _ => normPartitionWeight) t V Z = 0 := by
  by_contra h
  exact hscale (primaryAngularShortTupleSum_nonzero_scales ℓ X A a b q η t V hX hZ hVlo hVhi h)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothTuplePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit smooth partition inserted into finite convolution tuples.
Nonzero pieces automatically have the required product-length comparability. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normTupleWeight_partition {B : ℝ} {N : ℕ} (x : ι → ℝ)
    (hx : ∀ i, 1 ≤ x i) (hB : ∀ i, x i ≤ B) (hN : 2*B ≤ (4/3:ℝ)^N) :
    (∑ k : ι → Fin N, normTupleWeight k x) = 1 := by
  unfold normTupleWeight
  rw [← Fintype.prod_sum (fun (i : ι) (k : Fin N) =>
    normPartitionWeight (2*x i/(4/3:ℝ)^k.val))]
  have hi (i : ι) : (∑ k : Fin N, normPartitionWeight (2*x i/(4/3:ℝ)^k.val)) = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => normPartitionWeight (2*x i/(4/3:ℝ)^k))]
    exact normPartitionWeight_partition (hx i) (hB i) hN
  simp_rw [hi]
  simp

theorem finite_sum_normTupleWeight {κ : Type*} (S : Finset κ) (f : κ → ℂ)
    (x : κ → ι → ℝ) {B : ℝ} {N : ℕ}
    (hx : ∀ a ∈ S, ∀ i, 1 ≤ x a i) (hB : ∀ a ∈ S, ∀ i, x a i ≤ B)
    (hN : 2*B ≤ (4/3:ℝ)^N) :
    (∑ a ∈ S, f a) = ∑ k : ι → Fin N, ∑ a ∈ S, f a*normTupleWeight k (x a) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.mul_sum,normTupleWeight_partition (x a) (hx a ha) (hB a ha) hN,mul_one]

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

lemma normPartitionCount_covers {B : ℝ} (hB : 1 ≤ B) :
    2*B ≤ (4/3:ℝ)^normPartitionCount B := by
  have hr : 0 < Real.log (4/3:ℝ) := Real.log_pos (by norm_num)
  apply (Real.log_le_log_iff (by linarith : 0 < 2*B)
    (pow_pos (by norm_num : (0:ℝ) < 4/3) _)).mp
  rw [Real.log_pow]
  exact (div_le_iff₀ hr).mp (Nat.le_ceil _)

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

theorem normPartitionCount_power_bound (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
      (normPartitionCount B : ℝ)^d ≤ C*B^ε := by
  obtain ⟨K,hK,hcount⟩ := normPartitionCount_log_bound
  have hd : 0 < (d:ℝ)+1 := by positivity
  obtain ⟨A,hA,hlog⟩ := one_add_log_small_power (div_pos hε hd)
  refine ⟨(K*A)^d,pow_pos (mul_pos hK hA) _,?_⟩
  intro B hB
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hnb : (normPartitionCount B : ℝ) ≤ (K*A)*B^(ε/((d:ℝ)+1)) :=
    (hcount B hB).trans (by
      calc
        K*(1+Real.log B) ≤ K*(A*B^(ε/((d:ℝ)+1))) :=
          mul_le_mul_of_nonneg_left (hlog B hB) hK.le
        _ = _ := by ring)
  have he : ε/((d:ℝ)+1)*(d:ℝ) ≤ ε := by
    have hm := div_mul_cancel₀ ε hd.ne'
    have hp : 0 < ε/((d:ℝ)+1) := div_pos hε hd
    nlinarith
  calc
    _ ≤ ((K*A)*B^(ε/((d:ℝ)+1)))^d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hnb d
    _ = (K*A)^d*B^(ε/((d:ℝ)+1)*(d:ℝ)) := by
      rw [mul_pow,← Real.rpow_mul_natCast hBp.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hB he) (pow_nonneg (mul_pos hK hA).le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortTuplePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction of the original finite convolution from smooth
norm pieces. The common ball is forced by the global product cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_primary_pi (X : ι → ℝ) (f : (ι → Eisenstein) → ℂ) :
    (∑ n : (i : ι) → primaryElementBall (X i), f (fun i => n i)) =
      ∑ n ∈ Fintype.piFinset (fun i => primaryElementBall (X i)), f n := by
  apply Finset.sum_bij (fun n _ i => (n i : Eisenstein))
  · intro n _
    exact Fintype.mem_piFinset.mpr (fun i => (n i).property)
  · intro n _ m _ h
    funext i
    exact Subtype.ext (congrFun h i)
  · intro n hn
    exact ⟨fun i => ⟨n i,(Fintype.mem_piFinset.mp hn) i⟩,Finset.mem_univ _,rfl⟩
  · intro n _
    rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularShortTuplePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction of the original finite convolution from smooth
norm pieces. The common ball is forced by the global product cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primaryAngularShortTupleSum_eq_core (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) (Z : ℝ) :
    primaryAngularShortTupleSum ℓ X A a b q η (fun _ => normPartitionWeight) t V Z =
      ∑ n ∈ Fintype.piFinset (fun i => primaryElementBall (X i)),
        primaryAngularTupleCore ℓ A a b q η t V Z n*
          ∏ i, normPartitionWeight (norm (n i)/(X i/2)) := by
  unfold primaryAngularShortTupleSum
  calc
    _ = ∑ n : (i : ι) → primaryElementBall (X i),
        primaryAngularTupleCore ℓ A a b q η t V Z (fun i => n i)*
          ∏ i, normPartitionWeight (norm (n i)/(X i/2)) := by
      apply Finset.sum_congr rfl
      intro n _
      unfold primaryAngularTupleCore
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := sum_primary_pi X (fun n => primaryAngularTupleCore ℓ A a b q η t V Z n*
      ∏ i, normPartitionWeight (norm (n i)/(X i/2)))

omit [DecidableEq ι] in
lemma primaryAngularTupleCore_support (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (hV : ∀ x, 2 < x → V x = 0)
    (n : ι → Eisenstein) (hn : ∀ i, primary (n i))
    (h : primaryAngularTupleCore ℓ A a b q η t V Z n ≠ 0) (i : ι) : norm (n i) ≤ 2*Z := by
  have hv := (mul_ne_zero_iff.mp h).2
  have hp : (∏ j, norm (n j))/Z ≤ 2 := by
    by_contra hgt
    exact hv (hV _ (lt_of_not_ge hgt))
  have hni : norm (n i) ≤ ∏ j, norm (n j) := by
    calc
      _ = ∏ j ∈ ({i} : Finset ι), norm (n j) := by simp
      _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le (by simp)
        (fun j _ => norm_nonneg _) (fun j _ _ => one_le_norm (primary_ne_zero (hn j)))
  exact hni.trans ((div_le_iff₀ hZ).mp hp)

lemma primaryAngularShortTupleSum_common_ball (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (hV : ∀ x, 2 < x → V x = 0)
    (hX : ∀ i, 0 < X i) :
    primaryAngularShortTupleSum ℓ X A a b q η (fun _ => normPartitionWeight) t V Z =
      ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Z)),
        primaryAngularTupleCore ℓ A a b q η t V Z n*
          ∏ i, normPartitionWeight (norm (n i)/(X i/2)) := by
  rw [primaryAngularShortTupleSum_eq_core ℓ]
  apply Finset.sum_bij_ne_zero (fun n _ _ => n)
  · intro n hn h
    have hc := (mul_ne_zero_iff.mp h).1
    exact Fintype.mem_piFinset.mpr (fun i => mem_primaryElementBall.mpr
      ⟨(mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1,
        primaryAngularTupleCore_support ℓ A a b q η t V hZ hV n
          (fun j => (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) j)).1) hc i⟩)
  · intro n _ _ m _ _ h
    exact h
  · intro n hn h
    refine ⟨n,Fintype.mem_piFinset.mpr (fun i => ?_),h,rfl⟩
    have hw := (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp h).2) i (Finset.mem_univ i)
    exact mem_primaryElementBall.mpr
      ⟨(mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1,
        (normPartitionWeight_nonzero_length (hX i) hw).1⟩
  · intro n _ _
    rfl

/-- The unsplit finite tuple sum is exactly the sum of its explicit smooth
pieces. No decomposition hypothesis is assumed. -/
theorem primaryAngularShortTupleSum_partition (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hZ : 1 ≤ Z) (hV : ∀ x, 2 < x → V x = 0) :
    (∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Z)),
      primaryAngularTupleCore ℓ A a b q η t V Z n) =
      ∑ k : ι → Fin (normPartitionCount (2*Z)),
        primaryAngularShortTupleSum ℓ (fun i => (4/3:ℝ)^(k i).val) A a b q η
          (fun _ => normPartitionWeight) t V Z := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  rw [finite_sum_normTupleWeight (Fintype.piFinset (fun _ : ι => primaryElementBall (2*Z)))
    (primaryAngularTupleCore ℓ A a b q η t V Z) (fun n i => norm (n i))
    (fun n hn i => one_le_norm (primary_ne_zero
      (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1))
    (fun n hn i => (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).2)
    (normPartitionCount_covers (by linarith : 1 ≤ 2*Z))]
  apply Finset.sum_congr rfl
  intro k _
  rw [primaryAngularShortTupleSum_common_ball ℓ _ A a b q η t V hZp hV
    (fun i => pow_pos (by norm_num) _)]
  apply Finset.sum_congr rfl
  intro n _
  unfold normTupleWeight
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PartitionMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the explicit smooth norm partition loses only a small part of
an established power saving. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_piece_moment {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (f : κ → ρ → ℂ) :
    (∑ r, ‖∑ k, f k r‖^2) ≤ (Fintype.card κ:ℝ)*(∑ k, ∑ r, ‖f k r‖^2) := by
  calc
    _ ≤ ∑ r, (Fintype.card κ:ℝ)*(∑ k, ‖f k r‖^2) := by
      apply Finset.sum_le_sum
      intro r _
      apply (pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_sum_le _ _) 2).trans
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : κ => (1:ℝ))
        (fun k => ‖f k r‖)
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_partition_moment_power {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ Y : ℝ, T ≤ Y → ∀ (ρ : Type*) [Fintype ρ]
      (f : (ι → Fin (normPartitionCount (2*Y))) → ρ → ℂ),
      (∀ k, (∑ r, ‖f k r‖^2) ≤ Y^(7/3-ε)) →
      (∑ r, ‖∑ k, f k r‖^2) ≤ Y^(7/3-ε/2) := by
  obtain ⟨C,hC,hcount⟩ := normPartitionCount_power_bound (2*Fintype.card ι)
    (show 0 < ε/4 by linarith)
  let K : ℝ := C*2^(ε/4)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < ε/4 by linarith)).eventually_ge_atTop K)
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y hY ρ _ f hf
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hc : ((Fintype.card (ι → Fin (normPartitionCount (2*Y)))):ℝ)^2 ≤ K*Y^(ε/4) := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,← pow_mul]
    rw [Nat.mul_comm]
    apply (hcount (2*Y) (by linarith)).trans_eq
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hYp.le]
    dsimp [K]
    ring
  calc
    _ ≤ (Fintype.card (ι → Fin (normPartitionCount (2*Y))):ℝ)*
        (∑ k, ∑ r, ‖f k r‖^2) := finite_piece_moment f
    _ ≤ (Fintype.card (ι → Fin (normPartitionCount (2*Y))):ℝ)^2*Y^(7/3-ε) := by
      calc
        _ ≤ (Fintype.card (ι → Fin (normPartitionCount (2*Y))):ℝ)*
            (∑ _k : ι → Fin (normPartitionCount (2*Y)), Y^(7/3-ε)) := by
          apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hf k))
            (Nat.cast_nonneg _)
        _ = _ := by simp; ring
    _ ≤ (K*Y^(ε/4))*Y^(7/3-ε) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hYp.le _)
    _ = K*Y^(7/3-3*ε/4) := by
      rw [mul_assoc,← Real.rpow_add hYp,
        show ε/4+(7/3-ε) = 7/3-3*ε/4 by ring]
    _ ≤ Y^(ε/4)*Y^(7/3-3*ε/4) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularBalancedUnsplitNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact norm-partition reconstruction preserves the exceptional neighborhood. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_balanced_unsplit_tuple_neighborhood (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → F ≤ 2*Y → (∀ i, ShortArithmeticFactor F (A i)) →
      (∀ i, q i ≠ 0) → (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryAngularUnsplitTuple ℓ A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t V Y‖^2) ≤ Y^(7/3-ε) := by
  let D : ℝ := 2^(Fintype.card ι+1)
  have hD1 : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hD2 : 2 ≤ D := by
    dsimp [D]
    rw [pow_succ]
    have h := one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := Fintype.card ι)
    linarith
  have hD : 0 < D := zero_lt_one.trans_le hD1
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hw⟩ := angular_balanced_weighted_tuple_neighborhood (ι := ι) hpub ℓ hHuxley V hV hpos hsm hGI hGQ hD
  obtain ⟨T₁,hT₁,hpart⟩ := norm_partition_moment_power (ι := ι) hε
  refine ⟨κ,hκ,hκhi,ε/2,by positivity,max T T₁,?_⟩
  intro F Y A q η t P hY hF hA hq hη hqY ht hP
  have hYT : T ≤ Y := (le_max_left _ _).trans hY
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans hY
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  let f : (ι → Fin (normPartitionCount (2*Y))) → P → ℂ := fun k a =>
    primaryAngularShortTupleSum ℓ (fun i => (4/3:ℝ)^(k i).val) A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η
      (fun _ => normPartitionWeight) t V Y
  have hf (k : ι → Fin (normPartitionCount (2*Y))) : (∑ a : P, ‖f k a‖^2) ≤ Y^(7/3-ε) := by
    by_cases hg : Y ≤ (∏ i, (4/3:ℝ)^(k i).val) ∧ (∏ i, (4/3:ℝ)^(k i).val) ≤ D*Y
    · have h := hw F Y (fun i => (4/3:ℝ)^(k i).val) A q η t P Y hYT
        (hF.trans (mul_le_mul_of_nonneg_right hD2 hYp.le)) hA
        (fun i => one_le_pow₀ (by norm_num)) ((div_le_self hYp.le hD1).trans hg.1)
        hg.2 hq hη hqY ht hP hYp
      change (∑ a ∈ P.attach, ‖f k a‖^2) ≤ _
      dsimp only [f]
      rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
        ‖primaryAngularShortTupleSum ℓ (fun i => (4/3:ℝ)^(k i).val) A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η
          (fun _ => normPartitionWeight) t V Y‖^2)]
      exact h
    · have hz (a : P) : f k a = 0 := primaryAngularShortTupleSum_zero_outside_scales ℓ _ A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t V
        (fun i => pow_pos (by norm_num) _) hYp hVlo hVhi hg
      simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]
      exact Real.rpow_nonneg hYp.le _
  have hm := hpart Y hYT₁ P f hf
  have he (a : Eisenstein × Eisenstein) : primaryAngularUnsplitTuple ℓ A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t V Y =
      ∑ k : ι → Fin (normPartitionCount (2*Y)),
        primaryAngularShortTupleSum ℓ (fun i => (4/3:ℝ)^(k i).val) A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η
          (fun _ => normPartitionWeight) t V Y :=
    primaryAngularShortTupleSum_partition ℓ A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t V hY1 hVhi
  simp_rw [he]
  change (∑ a ∈ P.attach, ‖∑ k, f k a‖^2) ≤ _ at hm
  dsimp only [f] at hm
  rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
    ‖∑ k : ι → Fin (normPartitionCount (2*Y)),
      primaryAngularShortTupleSum ℓ (fun i => (4/3:ℝ)^(k i).val) A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η
        (fun _ => normPartitionWeight) t V Y‖^2)] at hm
  exact hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IndependentMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation of independent coordinate weights on a finite
arithmetic sum. The joint weight has explicitly factored L1 mass. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma zeroLineMellin_point (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {N X : ℝ} (hN : 0 < N) (hX : 0 < X) :
    W (N/X) = ∫ τ : ℝ, zeroLineMellinWeight W X τ*mellinPhase (-τ) N := by
  have h : W (N/X) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W ((τ:ℂ)*Complex.I)*(X:ℂ)^((τ:ℂ)*Complex.I)*
        (N:ℂ)^(-((τ:ℂ)*Complex.I)) := by
    simpa using smooth_mellin_finite (fun _ : Unit => (1:ℂ)) (fun _ : Unit => N)
      (fun _ => hN) W hW hpos hsm 0 hX
  rw [h,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with τ
  rw [mellinPhase_eq_cpow hN]
  have he : ((-τ:ℝ):ℂ)*Complex.I = -((τ:ℂ)*Complex.I) := by push_cast; ring
  rw [he]
  unfold zeroLineMellinWeight
  ring

lemma integrable_zeroLineMellin_phase (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) (N : ℝ) :
    Integrable (fun τ : ℝ => zeroLineMellinWeight W X τ*mellinPhase (-τ) N) := by
  have hw := zeroLineMellinWeight_integrable W hW hpos hsm hX
  have hp : Continuous (fun τ : ℝ => mellinPhase (-τ) N) := by
    unfold mellinPhase
    fun_prop
  apply hw.norm.mono' (hw.aestronglyMeasurable.mul hp.aestronglyMeasurable)
  filter_upwards with τ
  change ‖zeroLineMellinWeight W X τ*mellinPhase (-τ) N‖ ≤ ‖zeroLineMellinWeight W X τ‖
  rw [norm_mul,mellinPhase_norm,mul_one]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma independentMellinWeight_integrable (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) :
    Integrable (independentMellinWeight W X) :=
  Integrable.fintype_prod (fun i => zeroLineMellinWeight_integrable (W i) (hW i) (hpos i) (hsm i) (hX i))

lemma independentMellinWeight_mass (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i) :
    (∫ τ : ι → ℝ, ‖independentMellinWeight W X τ‖) = ∏ i, zeroLineMellinMass (W i) := by
  simp only [independentMellinWeight,norm_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun (i : ι) (t : ℝ) => ‖zeroLineMellinWeight (W i) (X i) t‖)]
  simp_rw [zeroLineMellinWeight_mass _ (hX _)]

/-- All original factor weights are separated simultaneously. No cutoff or
Mellin-tail assumption is used in this identity. -/
theorem independent_mellin_finite (a : κ → ℂ) (N : ι → κ → ℝ)
    (hN : ∀ i n, 0 < N i n) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) :
    (∑ n, a n*∏ i, W i (N i n/X i)) =
      ∫ τ : ι → ℝ, independentMellinWeight W X τ *
        ∑ n, a n*∏ i, mellinPhase (-(τ i)) (N i n) := by
  have hi (n : κ) : Integrable (fun τ : ι → ℝ =>
      a n*∏ i, zeroLineMellinWeight (W i) (X i) (τ i)*mellinPhase (-(τ i)) (N i n)) :=
    (Integrable.fintype_prod (fun i =>
      integrable_zeroLineMellin_phase (W i) (hW i) (hpos i) (hsm i) (hX i) (N i n))).const_mul (a n)
  calc
    _ = ∑ n, a n*∫ τ : ι → ℝ,
        ∏ i, zeroLineMellinWeight (W i) (X i) (τ i)*mellinPhase (-(τ i)) (N i n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [integral_fintype_prod_volume_eq_prod (fun (i : ι) (τ : ℝ) =>
        zeroLineMellinWeight (W i) (X i) τ*mellinPhase (-τ) (N i n))]
      simp_rw [← zeroLineMellin_point (W _) (hW _) (hpos _) (hsm _) (hN _ n) (hX _)]
    _ = ∫ τ : ι → ℝ, ∑ n, a n*
        ∏ i, zeroLineMellinWeight (W i) (X i) (τ i)*mellinPhase (-(τ i)) (N i n) := by
      simp_rw [← integral_const_mul]
      exact (integral_finsetSum _ (fun n _ => hi n)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with τ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.prod_mul_distrib]
      unfold independentMellinWeight
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularCoordinateWeightedTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent smooth weights on the original arithmetic factors, with the
exact Mellin representation by the unweighted convolutions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma primaryAngularTupleCore_shift (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t τ : ι → ℝ)
    (V : ℝ → ℂ) (Y : ℝ) (n : ι → Eisenstein) :
    primaryAngularTupleCore ℓ A a b q η t V Y n * ∏ i, mellinPhase (-(τ i)) (norm (n i)) =
      primaryAngularTupleCore ℓ A a b q η (fun i => t i-τ i) V Y n := by
  unfold primaryAngularTupleCore
  rw [mul_right_comm,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_assoc,mul_assoc,← mellinPhase_add]
  congr 2

lemma continuous_primaryAngularUnsplitTuple (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (V : ℝ → ℂ) (Y : ℝ) :
    Continuous (fun t : ι → ℝ => primaryAngularUnsplitTuple ℓ A a b q η t V Y) := by
  unfold primaryAngularUnsplitTuple primaryAngularTupleCore mellinPhase
  fun_prop

 theorem primaryAngularCoordinateWeightedTuple_mellin (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) :
    primaryAngularCoordinateWeightedTuple ℓ A a b q η t W X V Y =
      ∫ τ : ι → ℝ, independentMellinWeight W X τ *
        primaryAngularUnsplitTuple ℓ A a b q η (fun i => t i-τ i) V Y := by
  let S := Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y))
  have hN (i : ι) (n : S) : 0 < norm (n.val i) :=
    norm_pos_of_ne_zero (primary_ne_zero
      (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp n.property) i)).1)
  have hm := independent_mellin_finite
    (fun n : S => primaryAngularTupleCore ℓ A a b q η t V Y n.val)
    (fun i (n : S) => norm (n.val i)) hN W X hW hpos hsm hX
  have hl : (∑ n : S, primaryAngularTupleCore ℓ A a b q η t V Y n.val *
      ∏ i, W i (norm (n.val i)/X i)) = primaryAngularCoordinateWeightedTuple ℓ A a b q η t W X V Y := by
    change (∑ n ∈ S.attach, _) = _
    rw [Finset.sum_attach (f := fun n : ι → Eisenstein =>
      primaryAngularTupleCore ℓ A a b q η t V Y n * ∏ i, W i (norm (n i)/X i))]
    rfl
  rw [hl] at hm
  rw [hm]
  apply integral_congr_ae
  filter_upwards with τ
  congr 1
  simp_rw [primaryAngularTupleCore_shift ℓ]
  change (∑ n ∈ S.attach, primaryAngularTupleCore ℓ A a b q η (fun i => t i-τ i) V Y n.val) = _
  rw [Finset.sum_attach (f := fun n : ι → Eisenstein =>
    primaryAngularTupleCore ℓ A a b q η (fun i => t i-τ i) V Y n)]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryProductCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of ideal convolution coefficients with the finite
fibres of products of primary Eisenstein elements. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealExponentOf_primary_prod {ι : Type*} (S : Finset ι) (n : ι → Eisenstein)
    (hn : ∀ i ∈ S, primary (n i)) :
    idealExponentOf (∏ i ∈ S, n i) = ∑ i ∈ S, idealExponentOf (n i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty,Finset.sum_empty]
    simpa [idealExponentGenerator] using idealExponentOf_generator (0 : EisensteinIdealExponent)
  | @insert i S hi ih =>
    have hS : ∀ j ∈ S, primary (n j) := fun j hj => hn j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi,Finset.sum_insert hi,
      idealExponentOf_mul (primary_ne_zero (hn i (Finset.mem_insert_self _ _)))
        (primary_ne_zero (primary_finset_prod S n hS)),ih hS]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coeff_product_primary_fiber {R : Type*} [CommSemiring R]
    (A : ι → MvPowerSeries EisensteinIdealPrime R)
    {b : Eisenstein} (hb : primary b) {F : ℝ} (hbF : norm b ≤ F) :
    MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i) =
      ∑ n ∈ (Fintype.piFinset (fun _ : ι => primaryElementBall F)).filter
        (fun n => (∏ i, n i) = b), ∏ i, MvPowerSeries.coeff (idealExponentOf (n i)) (A i) := by
  rw [MvPowerSeries.coeff_prod]
  let g : (ι →₀ EisensteinIdealExponent) → ι → Eisenstein :=
    fun l i => idealPrimaryGenerator (l i)
  have hle (l : ι →₀ EisensteinIdealExponent)
      (hl : l ∈ Finset.finsuppAntidiag Finset.univ (idealExponentOf b)) (i : ι) :
      l i ≤ idealExponentOf b := by
    rw [← (Finset.mem_finsuppAntidiag.mp hl).1]
    exact Finset.single_le_sum (fun j _ => (show 0 ≤ l j from zero_le)) (Finset.mem_univ i)
  have hg (l : ι →₀ EisensteinIdealExponent)
      (hl : l ∈ Finset.finsuppAntidiag Finset.univ (idealExponentOf b)) :
      ∀ i, primary (g l i) := fun i => idealPrimaryGenerator_primary hb (hle l hl i)
  apply Finset.sum_bij (fun l _ => g l)
  · intro l hl
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => mem_primaryElementBall.mpr ⟨hg l hl i,?_⟩),?_⟩
    · rw [idealPrimaryGenerator_norm]
      exact ((idealExponentNorm_mono (hle l hl i)).trans_eq
        (idealExponentOf_norm (primary_ne_zero hb))).trans hbF
    · apply primary_eq_of_idealExponentOf_eq (primary_finset_prod _ _ (fun i _ => hg l hl i)) hb
      rw [idealExponentOf_primary_prod _ _ (fun i _ => hg l hl i)]
      simpa only [g,idealExponentOf_primaryGenerator] using (Finset.mem_finsuppAntidiag.mp hl).1
  · intro l _ m _ h
    apply Finsupp.ext
    intro i
    have hi := congrArg idealExponentOf (congrFun h i)
    simpa only [g,idealExponentOf_primaryGenerator] using hi
  · intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hnp (i : ι) : primary (n i) :=
      (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hmem.1) i)).1
    let l : ι →₀ EisensteinIdealExponent :=
      Finsupp.onFinset Finset.univ (fun i => idealExponentOf (n i)) (by simp)
    have hli (i : ι) : l i = idealExponentOf (n i) := rfl
    refine ⟨l,Finset.mem_finsuppAntidiag.mpr ⟨?_,Finset.subset_univ _⟩,?_⟩
    · simp_rw [hli]
      rw [← idealExponentOf_primary_prod _ _ (fun i _ => hnp i),hmem.2]
    · funext i
      exact idealPrimaryGenerator_at_element (hnp i)
  · intro l _
    apply Finset.prod_congr rfl
    intro i _
    simp only [g,idealExponentOf_primaryGenerator]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ComplexWeightedConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex coefficient collection retains the distinct norm and residue
twists of each original prime factor during short inversion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complex_coeff_product_eq_convolution (A : ι → MvPowerSeries EisensteinIdealPrime ℂ)
    {b : Eisenstein} (hb : primary b) {F : ℝ} (hbF : norm b ≤ F) :
    MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i) =
      orderedConvolution (fun _ : ι => primaryElementBall F)
        (fun i n => MvPowerSeries.coeff (idealExponentOf n) (A i)) b := by
  rw [coeff_product_primary_fiber A hb hbF]
  rfl

/-- The global smooth cutoff permits collection on one finite primary
ball, although the unrestricted product support is much larger. -/
theorem primaryComplexProductPolynomial_eq_tuple (A : ι → MvPowerSeries EisensteinIdealPrime ℂ)
    (χ : Eisenstein → ℂ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryComplexProductPolynomial A χ V Y =
      ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        (∏ i, MvPowerSeries.coeff (idealExponentOf (n i)) (A i))*
          χ (∏ i, n i)*V ((∏ i, norm (n i))/Y) := by
  let S : ι → Finset Eisenstein := fun _ => primaryElementBall (2*Y)
  let w : ι → Eisenstein → ℂ := fun i n =>
    MvPowerSeries.coeff (idealExponentOf n) (A i)
  have hc (b : Eisenstein) (hb : b ∈ primaryElementBall (2*Y)) :
      MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i) = orderedConvolution S w b :=
    complex_coeff_product_eq_convolution A (mem_primaryElementBall.mp hb).1 (mem_primaryElementBall.mp hb).2
  unfold primaryComplexProductPolynomial
  have hs : (∑ b ∈ primaryElementBall (2*Y), orderedConvolution S w b*(χ b*V (norm b/Y))) =
      ∑ b ∈ orderedConvolutionSupport S, orderedConvolution S w b*(χ b*V (norm b/Y)) := by
    apply Finset.sum_bij_ne_zero (fun b _ _ => b)
    · intro b _ hn
      by_contra hb
      rw [orderedConvolution_eq_zero_of_not_mem S w hb,zero_mul] at hn
      exact hn rfl
    · intro b _ _ c _ _ h
      exact h
    · intro b hb hn
      have hp : primary b := by
        change b ∈ (Fintype.piFinset S).image (fun n => ∏ i, n i) at hb
        obtain ⟨n,hnmem,rfl⟩ := Finset.mem_image.mp hb
        have hn' : n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)) := hnmem
        have hni (i : ι) : n i ∈ primaryElementBall (2*Y) := (Fintype.mem_piFinset.mp hn') i
        exact primary_finset_prod Finset.univ n (fun i _ => (mem_primaryElementBall.mp (hni i)).1)
      have hv : V (norm b/Y) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).2).2
      have hbn : norm b ≤ 2*Y := by
        by_contra hgt
        exact hv (hV _ ((lt_div_iff₀ hY).mpr (lt_of_not_ge hgt)))
      exact ⟨b,mem_primaryElementBall.mpr ⟨hp,hbn⟩,hn,rfl⟩
    · intro b _ _
      rfl
  calc
    _ = ∑ b ∈ primaryElementBall (2*Y), orderedConvolution S w b*χ b*V (norm b/Y) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hc b hb]
    _ = ∑ b ∈ primaryElementBall (2*Y), orderedConvolution S w b*(χ b*V (norm b/Y)) := by
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := hs
    _ = _ := by
      rw [orderedConvolution_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [norm_finset_prod]
      dsimp only [w]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleSize
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial bound for the actual von Mangoldt tuple sum. This coarse
bound is used only against arbitrarily rapid Mellin tails. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma vonMangoldt_coeff_norm_le {Y : ℝ} {n : Eisenstein}
    (hn : n ∈ primaryElementBall (2*Y)) :
    ‖((MvPowerSeries.coeff (idealExponentOf n) idealVonMangoldt:ℝ):ℂ)‖ ≤ 2*Y := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  have hp := (mem_primaryElementBall.mp hn).1
  have h := idealVonMangoldt_coeff_abs_le_logNorm (idealExponentOf n)
  rw [idealExponentOf_norm (primary_ne_zero hp)] at h
  exact h.trans ((Real.log_le_self (norm_nonneg n)).trans (mem_primaryElementBall.mp hn).2)

lemma vonMangoldt_tuple_core_bound (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (V : ℝ → ℂ)
    {M Y : ℝ} (_hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y)
    (n : ι → Eisenstein) (hn : n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y))) :
    ‖primaryTupleCore (fun _ : ι => idealVonMangoldt) a b q η t V Y n‖ ≤
      (2*Y)^(Fintype.card ι)*M := by
  have hi (i : ι) :
      ‖((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*mellinPhase (t i) (norm (n i)))‖ ≤ 2*Y := by
    have htw : ‖mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
        mellinPhase (t i) (norm (n i))‖ ≤ 1 := by
      rw [norm_mul,mellinPhase_norm,mul_one,norm_mul]
      exact (mul_le_mul (norm_mixedCubic_le_one ha hb _) (residueChar_norm_le_one (hq i) (η i) _)
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (_root_.norm_nonneg _) htw).trans
      (vonMangoldt_coeff_norm_le ((Fintype.mem_piFinset.mp hn) i))
  unfold primaryTupleCore
  rw [norm_mul,norm_prod]
  have hp : (∏ i, ‖((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*mellinPhase (t i) (norm (n i)))‖) ≤
      (2*Y)^(Fintype.card ι) := by
    calc
      _ ≤ ∏ _i : ι, 2*Y :=
        Finset.prod_le_prod (fun i _ => _root_.norm_nonneg _) (fun i _ => hi i)
      _ = _ := by simp
  exact mul_le_mul hp (hV _) (_root_.norm_nonneg _) (pow_nonneg (by positivity) _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeTupleSize
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma angularTupleCore_norm (ℓ : ℤ) (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) (Y : ℝ) (n : ι → Eisenstein) (hn : ∀ i, n i ≠ 0) :
    ‖primaryAngularTupleCore ℓ A a b q η t V Y n‖ =
      ‖primaryTupleCore A a b q η t V Y n‖ := by
  have he : primaryAngularTupleCore ℓ A a b q η t V Y n =
      (∏ i, theta ℓ (n i))*primaryTupleCore A a b q η t V Y n := by
    unfold primaryAngularTupleCore primaryTupleCore
    rw [← mul_assoc,← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    ring
  rw [he,norm_mul,norm_prod]
  simp only [norm_theta (hn _) ℓ,Finset.prod_const_one,one_mul]

lemma angular_vonMangoldt_tuple_core_bound (ℓ : ℤ) (a b : Eisenstein)
    (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (V : ℝ → ℂ)
    {M Y : ℝ} (hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y)
    (n : ι → Eisenstein) (hn : n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y))) :
    ‖primaryAngularTupleCore ℓ (fun _ : ι => idealVonMangoldt) a b q η t V Y n‖ ≤
      (2*Y)^(Fintype.card ι)*M := by
  rw [angularTupleCore_norm ℓ _ _ _ _ _ _ _ _ _ (fun i =>
    primary_ne_zero (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1)]
  exact vonMangoldt_tuple_core_bound a b ha hb q η hq t V hM hV hY n hn

 theorem angular_vonMangoldt_unsplit_size (ℓ : ℤ) (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (V : ℝ → ℂ)
    {M Y : ℝ} (hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y) :
    ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt) a b q η t V Y‖ ≤
      (M*72^(Fintype.card ι))*Y^(2*Fintype.card ι) := by
  unfold primaryAngularUnsplitTuple
  calc
    _ ≤ ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        ‖primaryAngularTupleCore ℓ (fun _ : ι => idealVonMangoldt) a b q η t V Y n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        (2*Y)^(Fintype.card ι)*M :=
      Finset.sum_le_sum (fun n hn => angular_vonMangoldt_tuple_core_bound ℓ a b ha hb q η hq t V hM hV hY n hn)
    _ = ((primaryElementBall (2*Y)).card:ℝ)^(Fintype.card ι)*((2*Y)^(Fintype.card ι)*M) := by
      simp [Fintype.card_piFinset,Finset.prod_const]
    _ ≤ (36*Y)^(Fintype.card ι)*((2*Y)^(Fintype.card ι)*M) := by
      apply mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _) (mul_nonneg (pow_nonneg (by positivity) _) hM)
      nlinarith [primaryElementBall_card_le (show 0 ≤ 2*Y by positivity)]
    _ = M*((36*Y)*(2*Y))^(Fintype.card ι) := by
      rw [mul_pow (36*Y) (2*Y)]
      ring
    _ = M*(72*Y^2)^(Fintype.card ι) := by congr 1; congr 1; ring
    _ = _ := by rw [mul_pow,pow_mul]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IndependentMellinTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high-coordinate tail of the genuine product Mellin weight is bounded
by its explicit finite sum of coordinate moments. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma measurableSet_mellinHeightBox (T : ℝ) : MeasurableSet (mellinHeightBox (ι := ι) T) := by
  have he : mellinHeightBox (ι := ι) T = ⋂ i, {τ : ι → ℝ | |τ i| ≤ T} := by
    ext τ
    simp [mellinHeightBox]
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_pi_apply i).abs measurable_const)

omit [DecidableEq ι] in
lemma mellinHeightPower_nonneg (A : ℕ) (τ : ι → ℝ) : 0 ≤ mellinHeightPower A τ :=
  Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg (τ i)) A)

omit [DecidableEq ι] in
lemma mellinHeightPower_large {T : ℝ} (hT : 0 ≤ T) (A : ℕ) {τ : ι → ℝ}
    (hτ : τ ∈ (mellinHeightBox T)ᶜ) : T^A ≤ mellinHeightPower A τ := by
  have h : ∃ i, T < |τ i| := by
    simpa only [mellinHeightBox,mem_compl_iff,mem_ofPred_eq,not_forall,not_le] using hτ
  obtain ⟨i,hi⟩ := h
  exact (pow_le_pow_left₀ hT hi.le A).trans
    (Finset.single_le_sum (fun j _ => pow_nonneg (abs_nonneg (τ j)) A) (Finset.mem_univ i))

omit [DecidableEq ι] in
theorem multivariate_weighted_tail (w : (ι → ℝ) → ℂ) (hw : Integrable w)
    (A : ℕ) (hA : Integrable (fun τ => mellinHeightPower A τ*‖w τ‖))
    {T : ℝ} (hT : 0 < T) :
    (∫ τ in (mellinHeightBox T)ᶜ, ‖w τ‖) ≤
      (∫ τ : ι → ℝ, mellinHeightPower A τ*‖w τ‖)/T^A := by
  apply (le_div_iff₀ (pow_pos hT A)).mpr
  rw [mul_comm,← integral_const_mul]
  apply (integral_mono_ae (hw.norm.restrict.const_mul _) hA.restrict ?_).trans
    (setIntegral_le_integral hA (Filter.Eventually.of_forall
      (fun τ => mul_nonneg (mellinHeightPower_nonneg A τ) (_root_.norm_nonneg _))))
  filter_upwards [ae_restrict_mem (measurableSet_mellinHeightBox T).compl] with τ hτ
  exact mul_le_mul_of_nonneg_right (mellinHeightPower_large hT.le A hτ) (_root_.norm_nonneg _)

lemma prod_one_coordinate (f : ι → ℝ) (i : ι) (c : ℝ) :
    (∏ j, if j=i then c*f j else f j) = c*∏ j, f j := by
  classical
  have he (j : ι) : (if j=i then c*f j else f j) = (if j=i then c else 1)*f j := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp

lemma independentMellinWeight_coordinate_moment_integrable
    (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ) (i : ι) :
    Integrable (fun τ : ι → ℝ => |τ i|^A*‖independentMellinWeight W X τ‖) := by
  have hh (j : ι) : Integrable (fun t : ℝ =>
      if j=i then |t|^A*‖zeroLineMellinWeight (W j) (X j) t‖ else
        ‖zeroLineMellinWeight (W j) (X j) t‖) := by
    by_cases hj : j=i
    · simp only [hj,ite_true, if_true]
      exact zeroLineMellinWeight_moment_integrable (W i) (hW i) (hpos i) (hsm i) (hX i) A
    · simp only [hj,ite_false, if_false]
      exact (zeroLineMellinWeight_integrable (W j) (hW j) (hpos j) (hsm j) (hX j)).norm
  have hp := Integrable.fintype_prod hh
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  funext τ
  rw [independentMellinWeight,norm_prod]
  symm
  convert prod_one_coordinate (fun j => ‖zeroLineMellinWeight (W j) (X j) (τ j)‖) i (|τ i|^A) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j=i <;> simp [hj]

lemma independentMellinWeight_moment_integrable
    (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ) :
    Integrable (fun τ : ι → ℝ => mellinHeightPower A τ*‖independentMellinWeight W X τ‖) := by
  simp only [mellinHeightPower,Finset.sum_mul]
  exact integrable_finsetSum _ (fun i _ =>
    independentMellinWeight_coordinate_moment_integrable W X hW hpos hsm hX A i)

omit [DecidableEq ι] in
lemma independentMellinWeight_norm_scale (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (τ : ι → ℝ) :
    ‖independentMellinWeight W X τ‖ = ‖independentMellinWeight W (fun _ => 1) τ‖ := by
  simp only [independentMellinWeight,norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [zeroLineMellinWeight_norm (W i) (hX i),
    zeroLineMellinWeight_norm (W i) (by norm_num)]

omit [DecidableEq ι] in
lemma independentMellinMoment_nonneg (W : ι → ℝ → ℂ) (A : ℕ) :
    0 ≤ independentMellinMoment W A :=
  integral_nonneg (fun τ => mul_nonneg (mellinHeightPower_nonneg A τ) (_root_.norm_nonneg _))

omit [DecidableEq ι] in
lemma independentMellinWeight_moment (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (A : ℕ) :
    (∫ τ : ι → ℝ, mellinHeightPower A τ*‖independentMellinWeight W X τ‖) =
      independentMellinMoment W A := by
  simp_rw [independentMellinWeight_norm_scale W X hX]
  rfl

theorem independentMellinWeight_tail (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ)
    {T : ℝ} (hT : 0 < T) :
    (∫ τ in (mellinHeightBox T)ᶜ, ‖independentMellinWeight W X τ‖) ≤
      independentMellinMoment W A/T^A := by
  have h := multivariate_weighted_tail (independentMellinWeight W X)
    (independentMellinWeight_integrable W X hW hpos hsm hX) A
    (independentMellinWeight_moment_integrable W X hW hpos hsm hX A) hT
  rwa [independentMellinWeight_moment W X hX A] at h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IndependentMellinMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-row L2 transfer for independently separated norm weights, with a
proved tail outside the simultaneous height window. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
lemma finite_box_integral_moment (f : κ → (ι → ℝ) → ℂ)
    (hf : ∀ r, Continuous (f r)) (w : (ι → ℝ) → ℂ) (hw : Integrable w)
    (T B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ τ ∈ mellinHeightBox T, (∑ r, ‖f r τ‖^2) ≤ B) :
    (∑ r, ‖∫ τ in mellinHeightBox T, w τ*f r τ‖^2) ≤
      (∫ τ, ‖w τ‖)^2*B := by
  have hc : Continuous (fun τ => WithLp.toLp 2 (fun r => f r τ)) :=
    (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp (continuous_pi hf)
  have ha : ∀ᵐ τ ∂(volume.restrict (mellinHeightBox T)), (∑ r, ‖f r τ‖^2) ≤ B := by
    filter_upwards [ae_restrict_mem (measurableSet_mellinHeightBox T)] with τ hτ
    exact hb τ hτ
  have hm := finite_row_integral_moment f w hc.aestronglyMeasurable hw.restrict hB ha
  apply hm.trans
  have hmass : (∫ τ in mellinHeightBox T, ‖w τ‖) ≤ ∫ τ, ‖w τ‖ :=
    setIntegral_le_integral hw.norm (Filter.Eventually.of_forall (fun _ => _root_.norm_nonneg _))
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (integral_nonneg (fun _ => _root_.norm_nonneg _)) hmass 2) hB

theorem independent_mellin_integral_moment (f : κ → (ι → ℝ) → ℂ)
    (hf : ∀ r, Continuous (f r)) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ)
    {T L B : ℝ} (hT : 0 < T) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hsize : ∀ r τ, ‖f r τ‖ ≤ L)
    (hbound : ∀ τ ∈ mellinHeightBox T, (∑ r, ‖f r τ‖^2) ≤ B) :
    (∑ r, ‖∫ τ, independentMellinWeight W X τ*f r τ‖^2) ≤
      2*(∏ i, zeroLineMellinMass (W i))^2*B+
        2*(Fintype.card κ:ℝ)*((L/T^A)*independentMellinMoment W A)^2 := by
  let w := independentMellinWeight W X
  have hw : Integrable w := independentMellinWeight_integrable W X hW hpos hsm hX
  have hc := finite_box_integral_moment f hf w hw T B hB hbound
  rw [independentMellinWeight_mass W X hX] at hc
  let H := (L/T^A)*independentMellinMoment W A
  have ht (r : κ) : ‖∫ τ in (mellinHeightBox T)ᶜ, w τ*f r τ‖ ≤ H := by
    calc
      _ ≤ L*(∫ τ in (mellinHeightBox T)ᶜ, ‖w τ‖) := by
        rw [← integral_const_mul]
        apply norm_integral_le_of_norm_le (hw.norm.restrict.const_mul L)
        filter_upwards with τ
        rw [norm_mul,mul_comm L]
        exact mul_le_mul_of_nonneg_left (hsize r τ) (_root_.norm_nonneg _)
      _ ≤ L*(independentMellinMoment W A/T^A) :=
        mul_le_mul_of_nonneg_left (independentMellinWeight_tail W X hW hpos hsm hX A hT) hL
      _ = H := by dsimp [H]; ring
  have ha (r : κ) :
      ‖(∫ τ, w τ*f r τ)-(∫ τ in mellinHeightBox T, w τ*f r τ)‖ ≤ H := by
    have hi : Integrable (fun τ => w τ*f r τ) := (hw.norm.mul_const L).mono'
      (hw.aestronglyMeasurable.mul (hf r).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun τ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hsize r τ) (_root_.norm_nonneg _)))
    rw [← integral_add_compl (measurableSet_mellinHeightBox T) hi,add_sub_cancel_left]
    exact ht r
  calc
    _ ≤ ∑ r, (2*‖∫ τ in mellinHeightBox T, w τ*f r τ‖^2+2*H^2) :=
      Finset.sum_le_sum (fun r _ => norm_square_le_central_tail _ _ (ha r))
    _ = 2*(∑ r, ‖∫ τ in mellinHeightBox T, w τ*f r τ‖^2)+2*(Fintype.card κ:ℝ)*H^2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _ ≤ _ := by dsimp [H]; nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularCoordinatePrimeMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate Mellin transfer for the actual independently weighted
von Mangoldt tuple sum, with a polynomial bound for every tail row. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

 theorem angular_coordinate_vonMangoldt_moment_bound (r : κ → Eisenstein × Eisenstein)
    (hr : ∀ j, primary (r j).1 ∧ primary (r j).2)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i)
    (V : ℝ → ℂ) {M Y : ℝ} (hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y)
    (A : ℕ) {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hbound : ∀ τ ∈ mellinHeightBox T,
      (∑ j, ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt)
        (r j).1 (r j).2 q η (fun i => t i-τ i) V Y‖^2) ≤ B) :
    (∑ j, ‖primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt)
      (r j).1 (r j).2 q η t W X V Y‖^2) ≤
      2*(∏ i, zeroLineMellinMass (W i))^2*B+
        2*(Fintype.card κ:ℝ)*
          (((M*72^(Fintype.card ι))*Y^(2*Fintype.card ι)/T^A)*independentMellinMoment W A)^2 := by
  let f : κ → (ι → ℝ) → ℂ := fun j τ =>
    primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt) (r j).1 (r j).2 q η
      (fun i => t i-τ i) V Y
  have hf (j : κ) : Continuous (f j) :=
    (continuous_primaryAngularUnsplitTuple ℓ _ _ _ q η V Y).comp (by fun_prop)
  have hsize (j : κ) (τ : ι → ℝ) :
      ‖f j τ‖ ≤ (M*72^(Fintype.card ι))*Y^(2*Fintype.card ι) :=
    angular_vonMangoldt_unsplit_size ℓ _ _ (hr j).1 (hr j).2 q η hq _ V hM hV hY
  have hm := independent_mellin_integral_moment f hf W X hW hpos hsm hX A hT
    (show 0 ≤ (M*72^(Fintype.card ι))*Y^(2*Fintype.card ι) by positivity) hB hsize hbound
  have he (j : κ) := primaryAngularCoordinateWeightedTuple_mellin ℓ (fun _ : ι => idealVonMangoldt)
    (r j).1 (r j).2 q η t W X V Y hW hpos hsm hX
  simpa only [he] using hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularComplexWeightedConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

/-- Independent residue characters and Mellin heights remain attached to
individual factors after exact collection. -/
theorem angularTwistedProductPolynomial_eq_unsplit (A : ι → EisensteinArithmeticFunction)
    {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hη : ∀ i, AngularUnitCompatible (q i) (η i) ℓ)
    (t : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryComplexProductPolynomial (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i) (A i))
      (mixedCubic a b) V Y = primaryAngularUnsplitTuple ℓ A a b q η t V Y := by
  rw [primaryComplexProductPolynomial_eq_tuple _ _ V hY hV]
  unfold primaryAngularUnsplitTuple
  apply Finset.sum_congr rfl
  intro n hn
  have hp (i : ι) : primary (n i) :=
    (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1
  simp_rw [angularTwistArithmetic_coeff_primary ℓ _ _ (hη _) _ _ (hp _)]
  rw [mixedCubic_prod _ _ ha hb]
  unfold primaryAngularTupleCore
  rw [← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTwistedConvolutionNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exceptional moments for actual complex convolutions with an independent
residue character and Mellin height on each factor. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_balanced_twisted_convolution_neighborhood (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → F ≤ 2*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) → (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryComplexProductPolynomial (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i) (A i)) (mixedCubic a.1 a.2) V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hbound⟩ := angular_balanced_unsplit_tuple_neighborhood ℓ (ι := ι)
    hpub hHuxley V hV hpos hsm hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,ε,hε,max 1 T,?_⟩
  intro F Y A q η t P hY hF hA hq hη hqY ht hP
  have hYp : 0 < Y := zero_lt_one.trans_le ((le_max_left _ _).trans hY)
  have he (a : Eisenstein × Eisenstein) (ha : a ∈ P) :
      primaryComplexProductPolynomial (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i) (A i)) (mixedCubic a.1 a.2) V Y =
        primaryAngularUnsplitTuple ℓ A a.1 a.2 q η t V Y :=
    angularTwistedProductPolynomial_eq_unsplit ℓ A (hP a ha).1.1 (hP a ha).1.2.1
      q η hη t V hYp hVhi
  calc
    _ = ∑ a ∈ P, ‖primaryAngularUnsplitTuple ℓ A a.1 a.2 q η t V Y‖^2 :=
      Finset.sum_congr rfl (fun a ha => by rw [he a ha])
    _ ≤ _ := hbound F Y A q η t P
      ((le_max_right _ _).trans hY) hF hA hq hη hqY ht hP

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortConvolutionExpansion
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each term of the short Möbius product expansion is an actual finite
family of the three permitted arithmetic factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma shortBranchFactor_spec (F : ℝ) (S : Finset ι) (i : shortBranchIndex S) :
    ShortArithmeticFactor F (shortBranchFactor F S i) := by
  rcases i with ⟨i,j⟩ | ⟨i,j⟩
  · fin_cases j <;> simp [shortBranchFactor,ShortArithmeticFactor]
  · fin_cases j <;> simp [shortBranchFactor,ShortArithmeticFactor]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTwistedShortProducts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short inversion with a different residue character and Mellin height
on each original prime factor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

lemma angularTwistArithmetic_two (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A : EisensteinArithmeticFunction) :
    angularTwistArithmetic ℓ q η t (2*A) = 2*angularTwistArithmetic ℓ q η t A := by
  rw [two_mul,angularTwistArithmetic_add ℓ,two_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_twisted_short_product_coeff {F : ℝ} (hF : 0 ≤ F)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (t : ι → ℝ) (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν (∏ i, angularTwistArithmetic ℓ (q i) (η i) (t i) idealVonMangoldt) =
      MvPowerSeries.coeff ν (∏ i, angularTwistArithmetic ℓ (q i) (η i) (t i) (shortVonMangoldt F)) := by
  have h : ∀ S : Finset ι, ∀ κ : EisensteinIdealExponent, idealExponentNorm κ ≤ F →
      MvPowerSeries.coeff κ (∏ i ∈ S, angularTwistArithmetic ℓ (q i) (η i) (t i) idealVonMangoldt) =
      MvPowerSeries.coeff κ (∏ i ∈ S, angularTwistArithmetic ℓ (q i) (η i) (t i) (shortVonMangoldt F)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intros; rfl
    | @insert i S hi ih =>
      intro κ hκ
      rw [Finset.prod_insert hi,Finset.prod_insert hi,MvPowerSeries.coeff_mul,MvPowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have h₁ : p.1 ≤ κ := by rw [← he]; exact le_add_of_nonneg_right zero_le
      have h₂ : p.2 ≤ κ := by rw [← he]; exact le_add_of_nonneg_left zero_le
      rw [ih p.2 ((idealExponentNorm_mono h₂).trans hκ)]
      congr 1
      change ((MvPowerSeries.coeff p.1 idealVonMangoldt:ℝ):ℂ)*angularResidueNormTwist ℓ (q i) (η i) (t i) p.1 =
        ((MvPowerSeries.coeff p.1 (shortVonMangoldt F):ℝ):ℂ)*angularResidueNormTwist ℓ (q i) (η i) (t i) p.1
      rw [shortVonMangoldt_local hF p.1 ((idealExponentNorm_mono h₁).trans hκ)]
  exact h Finset.univ ν hν

lemma angular_twisted_branch_product (F : ℝ) (S : Finset ι) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) :
    (∏ j : shortBranchIndex S,
      angularTwistArithmetic ℓ (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor F S j)) =
      (∏ i ∈ S, angularTwistArithmetic ℓ (q i) (η i) (t i) (shortFourFactor F))*
        ∏ i ∈ Finset.univ\S, angularTwistArithmetic ℓ (q i) (η i) (t i) (shortTwoFactor F) := by
  rw [Fintype.prod_sum_type,Fintype.prod_prod_type,Fintype.prod_prod_type]
  simp only [shortBranchSource,shortBranchFactor,Fin.prod_univ_four,Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  simp only [← angularTwistArithmetic_mul ℓ]
  change (∏ x : S, angularTwistArithmetic ℓ (q x) (η x) (t x) (shortFourFactor F))*
    (∏ x : ↥(Finset.univ\S), angularTwistArithmetic ℓ (q x) (η x) (t x) (shortTwoFactor F)) = _
  rw [Finset.prod_coe_sort (s := S) (f := fun i => angularTwistArithmetic ℓ (q i) (η i) (t i) (shortFourFactor F)),
    Finset.prod_coe_sort (s := Finset.univ\S) (f := fun i => angularTwistArithmetic ℓ (q i) (η i) (t i) (shortTwoFactor F))]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTwistedPrimeExpansion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact short inversion with independent residue and norm twists on every
original von Mangoldt factor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma angular_twisted_short_series_expansion (F : ℝ) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) :
    (∏ i, angularTwistArithmetic ℓ (q i) (η i) (t i) (shortVonMangoldt F)) =
      ∑ S : Finset ι, MvPowerSeries.C (shortBranchScalar S)*
        ∏ j : shortBranchIndex S,
          angularTwistArithmetic ℓ (q (shortBranchSource S j)) (η (shortBranchSource S j))
            (t (shortBranchSource S j)) (shortBranchFactor F S j) := by
  simp_rw [shortVonMangoldt_two_four,angularTwistArithmetic_sub ℓ,angularTwistArithmetic_two ℓ]
  rw [Finset.prod_sub,Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro S _
  rw [angular_twisted_branch_product ℓ]
  have hp : (∏ i ∈ Finset.univ\S, 2*angularTwistArithmetic ℓ (q i) (η i) (t i) (shortTwoFactor F)) =
      (2 : MvPowerSeries EisensteinIdealPrime ℂ)^(Fintype.card ι-S.card)*
        ∏ i ∈ Finset.univ\S, angularTwistArithmetic ℓ (q i) (η i) (t i) (shortTwoFactor F) := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_sdiff_of_subset (Finset.subset_univ S),Finset.card_univ]
  rw [hp]
  simp only [shortBranchScalar,map_mul,map_pow,map_neg,map_one,map_ofNat]
  ring

theorem angular_twisted_prime_coeff_expansion {F : ℝ} (hF : 0 ≤ F)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν (∏ i, angularTwistArithmetic ℓ (q i) (η i) (t i) idealVonMangoldt) =
      ∑ S : Finset ι, shortBranchScalar S * MvPowerSeries.coeff ν
        (∏ j : shortBranchIndex S,
          angularTwistArithmetic ℓ (q (shortBranchSource S j)) (η (shortBranchSource S j))
            (t (shortBranchSource S j)) (shortBranchFactor F S j)) := by
  rw [angular_twisted_short_product_coeff ℓ hF q η t ν hν,
    angular_twisted_short_series_expansion ℓ F q η t,map_sum]
  simp only [MvPowerSeries.coeff_C_mul]

theorem primaryAngularTwistedPrimeWeight_expansion (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (χ : Eisenstein → ℂ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y) :
    primaryComplexProductPolynomial (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i) idealVonMangoldt) χ V Y =
      ∑ S : Finset ι, shortBranchScalar S * primaryComplexProductPolynomial
        (fun j : shortBranchIndex S =>
          angularTwistArithmetic ℓ (q (shortBranchSource S j)) (η (shortBranchSource S j))
            (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) χ V Y := by
  unfold primaryComplexProductPolynomial
  calc
    _ = ∑ b ∈ primaryElementBall (2*Y), ∑ S : Finset ι, shortBranchScalar S *
        MvPowerSeries.coeff (idealExponentOf b)
          (∏ j : shortBranchIndex S,
            angularTwistArithmetic ℓ (q (shortBranchSource S j)) (η (shortBranchSource S j))
              (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j))*χ b*V (norm b/Y) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hb' := mem_primaryElementBall.mp hb
      have hN : idealExponentNorm (idealExponentOf b) ≤ 2*Y := by
        simpa only [idealExponentOf_norm (primary_ne_zero hb'.1)] using hb'.2
      rw [angular_twisted_prime_coeff_expansion ℓ (by positivity : 0 ≤ 2*Y) q η t _ hN,
        Finset.sum_mul,Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteMomentSaving
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite linear combination preserves a positive moment saving. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_positive_lower_bound {κ : Type*} [Fintype κ] (e : κ → ℝ)
    (he : ∀ k, 0 < e k) : ∃ d : ℝ, 0 < d ∧ ∀ k, d ≤ e k := by
  classical
  have h : ∀ S : Finset κ, ∃ d : ℝ, 0 < d ∧ ∀ k ∈ S, d ≤ e k := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert k S hk ih =>
      obtain ⟨d,hd,hde⟩ := ih
      refine ⟨min d (e k),lt_min hd (he k),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hde j hj)
  obtain ⟨d,hd,hde⟩ := h Finset.univ
  exact ⟨d,hd,fun k => hde k (Finset.mem_univ k)⟩

theorem finite_weighted_moment_saving {κ : Type*} [Fintype κ]
    (e : κ → ℝ) (he : ∀ k, 0 < e k) (c : κ → ℂ) :
    ∃ d : ℝ, 0 < d ∧ ∃ T : ℝ, 1 ≤ T ∧ ∀ Y : ℝ, T ≤ Y →
      ∀ (ρ : Type*) [Fintype ρ] (f : κ → ρ → ℂ),
      (∀ k, (∑ r, ‖f k r‖^2) ≤ Y^(7/3-e k)) →
      (∑ r, ‖∑ k, c k*f k r‖^2) ≤ Y^(7/3-d) := by
  obtain ⟨d,hd,hde⟩ := finite_positive_lower_bound e he
  let C : ℝ := (Fintype.card κ)*(∑ k, ‖c k‖^2)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < d/2 by linarith)).eventually_ge_atTop C)
  refine ⟨d/2,by positivity,max 1 T,le_max_left _ _,?_⟩
  intro Y hY ρ _ f hf
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hf' (k : κ) : (∑ r, ‖f k r‖^2) ≤ Y^(7/3-d) :=
    (hf k).trans (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith [hde k]))
  calc
    _ ≤ (Fintype.card κ:ℝ)*(∑ k, ∑ r, ‖c k*f k r‖^2) :=
      finite_piece_moment (fun k r => c k*f k r)
    _ = (Fintype.card κ:ℝ)*(∑ k, ‖c k‖^2*(∑ r, ‖f k r‖^2)) := by
      simp_rw [norm_mul,mul_pow,← Finset.mul_sum]
    _ ≤ (Fintype.card κ:ℝ)*(∑ k, ‖c k‖^2*Y^(7/3-d)) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hf' k) (sq_nonneg _)))
        (Nat.cast_nonneg _)
    _ = C*Y^(7/3-d) := by rw [← Finset.sum_mul]; dsimp [C]; ring
    _ ≤ Y^(d/2)*Y^(7/3-d) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTwistedPrimeNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original von Mangoldt convolutions with independent factor twists inherit
the short-factor power saving by an exact finite expansion. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_balanced_twisted_vonMangoldt_neighborhood (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (Y : ℝ) (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)), Y₀ ≤ Y → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) → (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryComplexProductPolynomial (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i) idealVonMangoldt)
        (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y‖^2) ≤ Y^(7/3-ε) := by
  choose κ hκ hκhi e he T hb using fun S : Finset ι =>
    angular_balanced_twisted_convolution_neighborhood ℓ (ι := shortBranchIndex S) hpub hHuxley V hV hpos hsm hVlo hVhi hGI hGQ
  obtain ⟨κ₀,hκ₀,hκall⟩ := finite_positive_lower_bound κ hκ
  obtain ⟨d,hd,T₁,hT₁,hsave⟩ := finite_weighted_moment_saving e he (shortBranchScalar (ι := ι))
  refine ⟨min κ₀ (1/10000),by positivity,min_le_right _ _,d,hd,max T₁ (1+∑ S, |T S|),?_⟩
  intro Y q η t P hY hq hη hqY ht hP
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hYT (S : Finset ι) : T S ≤ Y := by
    have hS : |T S| ≤ ∑ U : Finset ι, |T U| :=
      Finset.single_le_sum (fun U _ => abs_nonneg (T U)) (Finset.mem_univ S)
    have hh : 1+∑ U : Finset ι, |T U| ≤ Y := (le_max_right _ _).trans hY
    linarith [le_abs_self (T S)]
  let f : Finset ι → P → ℂ := fun S a =>
    primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      angularTwistArithmetic ℓ (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y
  have hf (S : Finset ι) : (∑ a : P, ‖f S a‖^2) ≤ Y^(7/3-e S) := by
    have h := hb S (2*Y) Y (shortBranchFactor (2*Y) S)
      (fun j => q (shortBranchSource S j)) (fun j => η (shortBranchSource S j))
      (fun j => t (shortBranchSource S j)) P
      (hYT S) le_rfl (shortBranchFactor_spec (2*Y) S)
      (fun j => hq _) (fun j => hη _) (fun j => hqY _) (fun j => ht _)
      (fun a ha => ⟨(hP a ha).1,
        (hP a ha).2.1.trans (Real.rpow_le_rpow_of_exponent_le hY1
          (by have := (min_le_left κ₀ (1/10000)).trans (hκall S); linarith)),
        (hP a ha).2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hY1
          (by have := (min_le_left κ₀ (1/10000)).trans (hκall S); linarith)),(hP a ha).2.2.2⟩)
    change (∑ a ∈ P.attach, ‖f S a‖^2) ≤ _
    dsimp only [f]
    rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
      ‖primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      angularTwistArithmetic ℓ (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y‖^2)]
    exact h
  have hm := hsave Y hYT₁ P f hf
  simp_rw [primaryAngularTwistedPrimeWeight_expansion ℓ q η t _ V hYp]
  change (∑ a ∈ P.attach, ‖∑ S, shortBranchScalar S*f S a‖^2) ≤ _ at hm
  dsimp only [f] at hm
  rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
    ‖∑ S : Finset ι, shortBranchScalar S*
      primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      angularTwistArithmetic ℓ (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y‖^2)] at hm
  exact hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoordinateNeighborhoodPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint Mellin tail with the larger neighborhood row count. -/
noncomputable section
namespace CubicFirstMoment

lemma coordinate_neighborhood_tail_power (k : ℕ) {Y K J : ℝ} (hY : 0 < Y) :
    2*Y^4*((K*Y^(2*k)/(Y^(1/1000:ℝ))^(1000*(2*k+7)))*J)^2 =
      (2*K^2*J^2)*Y^(-10:ℝ) := by
  have hp : (Y^(1/1000:ℝ))^(1000*(2*k+7)) = Y^(2*k+7) := by
    rw [← Real.rpow_mul_natCast hY.le]
    have he : (1/1000:ℝ)*(1000*(2*k+7):ℕ) = ((2*k+7:ℕ):ℝ) := by push_cast; ring
    rw [he,Real.rpow_natCast]
  have hd : Y^(2*k)/Y^(2*k+7) = Y^(-7:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_sub hY]
    congr 1
    push_cast
    ring
  rw [hp,show K*Y^(2*k)/Y^(2*k+7) = K*(Y^(2*k)/Y^(2*k+7)) by ring,hd]
  have he : Y^4*(Y^(-7:ℝ))^2 = Y^(-10:ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le,← Real.rpow_natCast,← Real.rpow_add hY]
    norm_num
  calc
    _ = (2*K^2*J^2)*(Y^4*(Y^(-7:ℝ))^2) := by ring
    _ = _ := by rw [he]

lemma coordinate_neighborhood_tail_le_short_tail (k : ℕ) {Y K J : ℝ} (hY : 1 ≤ Y) :
    2*Y^4*((K*Y^(2*k)/(Y^(1/1000:ℝ))^(1000*(2*k+7)))*J)^2 ≤
      (2*K^2*J^2)*Y^(-42/5:ℝ) := by
  rw [coordinate_neighborhood_tail_power k (zero_lt_one.trans_le hY)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by positivity)

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

lemma UniformLogWeights.vertical_seminorms {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (M : ℝ) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i σ, |σ| ≤ M →
      SchwartzMap.seminorm ℝ k n
        (mellinVerticalSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) ≤ C := by
  obtain ⟨C,hC,hb⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded
      (fun p : ι × ℝ => mellinVerticalSchwartz (W p.1) (h.compact p.1)
        (h.positive p.1) (h.smooth p.1) p.2) |>.mp (h.vertical_bounded M) (k,n)
  exact ⟨C,hC,fun i σ hσ => (hb (i,σ) hσ).le⟩

lemma UniformLogWeights.mellin_norm_moment {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (M : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i σ, |σ| ≤ M →
      (∫ t : ℝ, |t|^k*‖mellin (W i) ((σ:ℂ)+(t:ℂ)*Complex.I)‖) ≤ C := by
  let n : ℕ := (volume : Measure ℝ).integrablePower
  obtain ⟨C₀,hC₀,h₀⟩ := h.vertical_seminorms M 0 0
  obtain ⟨C₁,hC₁,h₁⟩ := h.vertical_seminorms M (k+n) 0
  let A : ℝ := 2^n*(∫ t : ℝ, (1+‖t‖)^(-(n:ℝ)))
  have hA : 0 ≤ A := mul_nonneg (pow_nonneg (by norm_num) _)
    (integral_nonneg (fun _ => Real.rpow_nonneg (by positivity) _))
  refine ⟨A*(C₀+C₁),mul_nonneg hA (by positivity),?_⟩
  intro i σ hσ
  let F := mellinVerticalSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ
  have hb := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume F k 0
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hb
  change (∫ t : ℝ, |t|^k*‖F t‖) ≤ A*
    (SchwartzMap.seminorm ℝ 0 0 F+SchwartzMap.seminorm ℝ (k+n) 0 F) at hb
  calc
    _ = ∫ t : ℝ, |t|^k*‖F t‖ := by
      congr 1
      ext t
      rw [mellinVerticalSchwartz_apply]
    _ ≤ A*(SchwartzMap.seminorm ℝ 0 0 F+SchwartzMap.seminorm ℝ (k+n) 0 F) := hb
    _ ≤ A*(C₀+C₁) := mul_le_mul_of_nonneg_left
      (add_le_add (h₀ i σ hσ) (h₁ i σ hσ)) hA

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformCoordinateWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma UniformLogWeights.zeroLine_moment {γ : Type*} {W : γ → ℝ → ℂ}
    (h : UniformLogWeights W) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, (∫ t : ℝ, |t|^A*‖zeroLineMellinWeight (W i) 1 t‖) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := h.mellin_norm_moment 0 A
  refine ⟨(1/(2*Real.pi))*C,by positivity,?_⟩
  intro i
  rw [zeroLineMellinWeight_moment (W i) (by norm_num) A]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Complex.ofReal_zero,zero_add] using hbound i 0 (by norm_num)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma independentMellinMoment_factorization (W : ι → ℝ → ℂ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (A : ℕ) :
    independentMellinMoment W A = ∑ i, ∏ j,
      (∫ t : ℝ, if j=i then |t|^A*‖zeroLineMellinWeight (W j) 1 t‖
        else ‖zeroLineMellinWeight (W j) 1 t‖) := by
  unfold independentMellinMoment mellinHeightPower
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ =>
    independentMellinWeight_coordinate_moment_integrable W (fun _ => 1) hW hpos hsm
      (fun _ => by norm_num) A i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_fintype_prod_volume_eq_prod (fun (j : ι) (t : ℝ) =>
    if j=i then |t|^A*‖zeroLineMellinWeight (W j) 1 t‖
      else ‖zeroLineMellinWeight (W j) 1 t‖)]
  apply integral_congr_ae
  filter_upwards with τ
  rw [independentMellinWeight,norm_prod]
  symm
  convert prod_one_coordinate (fun j => ‖zeroLineMellinWeight (W j) 1 (τ j)‖)
    i (|τ i|^A) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j=i <;> simp [hj]

/-- One bound controls the product L1 mass and the genuine joint tail moment
for every member of a uniformly smooth coordinate family. -/
theorem UniformLogWeights.coordinate_moments {γ : Type*} {W : γ → ι → ℝ → ℂ}
    (h : UniformLogWeights (fun z : γ × ι => W z.1 z.2)) (A : ℕ) :
    ∃ C J : ℝ, 0 ≤ C ∧ 0 ≤ J ∧ ∀ u : γ,
      (∏ i, zeroLineMellinMass (W u i)) ≤ C ∧ independentMellinMoment (W u) A ≤ J := by
  obtain ⟨C₀,hC₀,h₀⟩ := h.zeroLine_moment 0
  obtain ⟨C₁,hC₁,h₁⟩ := h.zeroLine_moment A
  let K := max C₀ C₁
  have hK : 0 ≤ K := hC₀.trans (le_max_left _ _)
  refine ⟨K^(Fintype.card ι),(Fintype.card ι:ℝ)*K^(Fintype.card ι),
    pow_nonneg hK _,by positivity,?_⟩
  intro u
  have hmass (i : ι) : zeroLineMellinMass (W u i) ≤ K := by
    have hh := (h₀ (u,i)).trans (le_max_left C₀ C₁)
    simp only [pow_zero,one_mul] at hh
    rw [zeroLineMellinWeight_mass (W u i) (Z := 1) (by norm_num)] at hh
    exact hh
  constructor
  · calc
      _ ≤ ∏ _i : ι, K := Finset.prod_le_prod (fun i _ => zeroLineMellinMass_nonneg (W u i))
        (fun i _ => hmass i)
      _ = _ := by simp
  · rw [independentMellinMoment_factorization (W u) (fun i => h.compact (u,i))
        (fun i => h.positive (u,i)) (fun i => h.smooth (u,i)) A]
    calc
      _ ≤ ∑ _i : ι, K^(Fintype.card ι) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ∏ _j : ι, K := by
            apply Finset.prod_le_prod
            · intro j _
              exact integral_nonneg (fun t => by split_ifs <;> positivity)
            · intro j _
              by_cases hj : j=i
              · simp only [hj,ite_true, if_true]
                exact (h₁ (u,i)).trans (le_max_right _ _)
              · simp only [hj,ite_false, if_false]
                rw [zeroLineMellinWeight_mass (W u j) (Z := 1) (by norm_num)]
                exact hmass j
          _ = _ := by simp
      _ = _ := by simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DilatedMomentPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
namespace CubicFirstMoment

lemma eventual_dilated_shift_height_bound :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ t τ : ℝ,
      |t| ≤ Y^(721/2000:ℝ) → |τ| ≤ Y^(1/1000:ℝ) → |t-τ| ≤ Y^(361/1000:ℝ) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 1/2000 by norm_num)).eventually_ge_atTop (2:ℝ))
  refine ⟨max 1 T,?_⟩
  intro Y hY t τ ht hτ
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hτ' : |τ| ≤ Y^(721/2000:ℝ) := hτ.trans
    (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
  calc
    _ ≤ |t|+|τ| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le t 0 τ
    _ ≤ 2*Y^(721/2000:ℝ) := by linarith
    _ ≤ Y^(1/2000:ℝ)*Y^(721/2000:ℝ) :=
      mul_le_mul_of_nonneg_right (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularCommonCoordinateExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional exponent is chosen before the smooth-weight family.
Only the threshold depends on its derivative constants. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]


 theorem angular_balanced_common_coordinate_exponents (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      ∃ Y₀ : ℝ, ∀ (u : γ) (Y : ℝ) (X : ι → ℝ)
      (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → (∀ i, 0 < X i) → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt)
        (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t (W u) X V Y‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,e,he,T,hraw⟩ := angular_balanced_twisted_vonMangoldt_neighborhood ℓ (ι := ι)
    hpub hHuxley V hV hposV hsmV hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,min e (1/3)/2,by positivity,?_⟩
  intro W hW
  obtain ⟨M,hM⟩ := hV.exists_bound_of_continuous hsmV.continuous
  have hM0 : 0 ≤ M := (_root_.norm_nonneg (V 0)).trans (hM 0)
  let k := Fintype.card ι
  let A := 1000*(2*k+7)
  let K : ℝ := M*72^k
  obtain ⟨L,J,hL,hJ,hMoments⟩ := hW.coordinate_moments A
  obtain ⟨T₁,hshift⟩ := eventual_dilated_shift_height_bound
  obtain ⟨T₂,hT₂,habs⟩ := absorb_short_mellin_bounds he (2*L^2) (2*K^2*J^2)
    (by positivity) (by positivity)
  refine ⟨max 324 (max T (max T₁ T₂)),?_⟩
  intro u Y X q η t P hY hX hq hη hqY ht hP
  have hY324 : 324 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := by linarith
  have hYp : 0 < Y := by linarith
  have hYT : T ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hYT₂ : T₂ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hb (τ : ι → ℝ) (hτ : τ ∈ mellinHeightBox (Y^(1/1000:ℝ))) :
      (∑ a : P, ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt)
        (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η (fun i => t i-τ i) V Y‖^2) ≤ Y^(7/3-e) := by
    have hh := hraw Y q η (fun i => t i-τ i) P hYT hq hη hqY
      (fun i => hshift Y hYT₁ _ _ (ht i) (hτ i)) hP
    have heq (a : Eisenstein × Eisenstein) (ha : a ∈ P) :=
      angularTwistedProductPolynomial_eq_unsplit ℓ (fun _ : ι => idealVonMangoldt)
        (hP a ha).1.1 (hP a ha).1.2.1 q η hη (fun i => t i-τ i) V hYp hVhi
    have hh' : (∑ a ∈ P, ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt)
        (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η (fun i => t i-τ i) V Y‖^2) ≤ Y^(7/3-e) := by
      calc
        _ = ∑ a ∈ P, ‖primaryComplexProductPolynomial
            (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i-τ i) idealVonMangoldt) (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y‖^2 :=
          Finset.sum_congr rfl (fun a ha => by rw [heq a ha])
        _ ≤ _ := hh
    change (∑ a ∈ P.attach, ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt)
      (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η (fun i => t i-τ i) V Y‖^2) ≤ _
    rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
      ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η (fun i => t i-τ i) V Y‖^2)]
    exact hh'
  have hm := angular_coordinate_vonMangoldt_moment_bound ℓ (fun a : P => (a : Eisenstein × Eisenstein))
    (fun a => ⟨(hP a a.property).1.1,(hP a a.property).1.2.1⟩) q η hq t (W u) X
    (fun i => hW.compact (u,i)) (fun i => hW.positive (u,i))
    (fun i => hW.smooth (u,i)) hX V hM0 hM hYp.le A (Real.rpow_pos_of_pos hYp _)
    (Real.rpow_nonneg hYp.le _) hb
  have hcard : (Fintype.card P:ℝ) ≤ Y^4 := by
    have hLY : Y^(1/3+κ) ≤ Y := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY1
        (by linarith : 1/3+κ ≤ 1)
    simpa only [Fintype.card_coe] using neighborhood_balanced_card P hY324
      (Real.rpow_nonneg hYp.le _) hLY
      (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.1⟩)
  have hm' : (∑ a ∈ P, ‖primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt)
      (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t (W u) X V Y‖^2) ≤ 2*L^2*Y^(7/3-e)+
        2*(Fintype.card P:ℝ)*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := by
    change (∑ a ∈ P.attach, _) ≤ _ at hm
    rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
      ‖primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t (W u) X V Y‖^2)] at hm
    have hmass0 : 0 ≤ ∏ i, zeroLineMellinMass (W u i) :=
      Finset.prod_nonneg (fun i _ => zeroLineMellinMass_nonneg _)
    have hjoint0 := independentMellinMoment_nonneg (W u) A
    apply hm.trans
    gcongr
    · exact (hMoments u).1
    · exact (hMoments u).2
  calc
    _ ≤ 2*L^2*Y^(7/3-e)+2*(Fintype.card P:ℝ)*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := hm'
    _ ≤ 2*L^2*Y^(7/3-e)+2*Y^4*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := by gcongr
    _ ≤ 2*L^2*Y^(7/3-e)+(2*K^2*J^2)*Y^(-42/5:ℝ) := by
      exact add_le_add le_rfl (coordinate_neighborhood_tail_le_short_tail (K := K) (J := J) k hY1)
    _ ≤ _ := habs Y hYT₂

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothLogDenominator
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth, globally defined extensions of the logarithmic denominator
weights. The extension equals the literal reciprocal on the application
range, so no pole can interfere with parameter-uniform differentiation. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace CubicFirstMoment

lemma positiveSmoothExtension_eq {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    positiveSmoothExtension c x = x := by
  have h : 1 ≤ 2*x/c-1 := by
    have hd : 2 ≤ 2*x/c := (le_div_iff₀ hc).mpr (by linarith)
    linarith
  simp [positiveSmoothExtension,Real.smoothTransition.one_of_one_le h]

lemma smoothReciprocal_eq {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    smoothReciprocal c x = x⁻¹ := by
  simp only [smoothReciprocal,positiveSmoothExtension_eq hc hx]

lemma smoothLog_eq {x : ℝ} (hx : 1 ≤ x) : smoothLog x = Real.log x := by
  simp only [smoothLog,positiveSmoothExtension_eq (by norm_num : (0:ℝ) < 1) hx]

lemma logDenominatorWeight_eq {c : ℝ} (hc : 0 < c) (w : ℝ → ℂ)
    {p : ℝ × ℝ} (ha : c ≤ p.1) (ht : 0 ≤ p.2) {x : ℝ} (hx : 1 ≤ x) :
    logDenominatorWeight c w p x = w x/(p.1+p.2*Real.log x:ℝ) := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hd : c ≤ p.1+p.2*Real.log x := by nlinarith
  rw [logDenominatorWeight,smoothLog_eq hx,smoothReciprocal_eq hc hd]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogReplacement
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact replacement of a prime indicator by von Mangoldt divided by log norm.
The discrepancy is bounded and is supported on actual higher primary prime powers. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_norm_gt_one {p : Eisenstein} (hp : Prime p) : 1 < norm p := by
  have hn := one_le_norm hp.ne_zero
  apply lt_of_le_of_ne hn
  intro he
  exact hp.not_isUnit (isUnit_of_norm_eq_one he.symm)

lemma normalizedVonMangoldt_at_prime {p : Eisenstein} (hp : Prime p) :
    normalizedVonMangoldt p = 1 := by
  rw [normalizedVonMangoldt,idealVonMangoldt_at_prime hp]
  exact div_self (Real.log_pos (prime_norm_gt_one hp)).ne'

lemma normalizedVonMangoldt_nonneg {a : Eisenstein} (ha : primary a) :
    0 ≤ normalizedVonMangoldt a :=
  div_nonneg (idealVonMangoldt_coeff_nonneg _)
    (Real.log_nonneg (one_le_norm (primary_ne_zero ha)))

lemma normalizedVonMangoldt_le_one {a : Eisenstein} (ha : primary a) :
    normalizedVonMangoldt a ≤ 1 := by
  have hlog : 0 ≤ Real.log (norm a) := Real.log_nonneg (one_le_norm (primary_ne_zero ha))
  have hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≤ Real.log (norm a) := by
    simpa only [idealExponentOf_norm (primary_ne_zero ha)] using
      idealVonMangoldt_coeff_le_logNorm (idealExponentOf a)
  by_cases hz : Real.log (norm a) = 0
  · simp only [normalizedVonMangoldt,hz,div_zero]
    norm_num
  · exact (div_le_one (lt_of_le_of_ne hlog (Ne.symm hz))).mpr hΛ

lemma primeLogCorrection_at_prime {p : Eisenstein} (hp : Prime p) :
    primeLogCorrection p = 0 := by
  simp only [primeLogCorrection,normalizedVonMangoldt_at_prime hp,primeIndicator,
    ite_eq_left hp,sub_self]

lemma primeLogCorrection_support {a : Eisenstein} (ha : primary a)
    (he : primeLogCorrection a ≠ 0) :
    ∃ p : Eisenstein, ∃ j : ℕ, primaryPrime p ∧ 2 ≤ j ∧ a = p^j := by
  have hp : ¬ Prime a := fun hp => he (primeLogCorrection_at_prime hp)
  have hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≠ 0 := by
    intro hz
    apply he
    simp only [primeLogCorrection,primeIndicator,ite_eq_right hp,normalizedVonMangoldt,hz,
      zero_div,sub_self]
  exact idealVonMangoldt_primary_nonprime_support ha hp hΛ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual error in replacing a convolution of prime indicators by
normalized von Mangoldt coefficients has sparse prime-power support. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeLogConvolutionError_sum (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (b : Eisenstein) :
    primeLogConvolutionError S w b =
      ∑ f ∈ (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b),
        ((∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i))-
          ∏ i, (primeIndicator (f i):ℂ)*w i (f i)) := by
  unfold primeLogConvolutionError orderedConvolution
  rw [Finset.sum_sub_distrib]

lemma primeLogConvolutionError_support_of_norm_le (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {Y c : ℝ}
    (hS : ∀ i, ∀ a ∈ S i, primary a ∧ Y^c < norm a)
    {b : Eisenstein} (hbY : norm b ≤ Y) (hb : primeLogConvolutionError S w b ≠ 0) :
    b ∈ largePrimePowerSupport Y c := by
  rw [primeLogConvolutionError_sum] at hb
  obtain ⟨f,hf,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
  have hex : ∃ i, primeLogCorrection (f i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    have he : (∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i)) =
        ∏ i, (primeIndicator (f i):ℂ)*w i (f i) := by
      apply Finset.prod_congr rfl
      intro i _
      have hi : normalizedVonMangoldt (f i) = primeIndicator (f i) :=
        sub_eq_zero.mp (h i)
      rw [hi]
    exact sub_eq_zero.mpr he
  obtain ⟨i,hi⟩ := hex
  have hfi := hS i (f i) (Fintype.mem_piFinset.mp hfs i)
  obtain ⟨p,j,hp,hj,he⟩ := primeLogCorrection_support hfi.1 hi
  have hprod0 : (∏ i, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => primary_ne_zero (hS i (f i) (Fintype.mem_piFinset.mp hfs i)).1)
  refine Finset.mem_filter.mpr ⟨mem_nonzeroNormBall.mpr
    ⟨hbY,hfb ▸ hprod0⟩,p,j,hp,hj,?_,?_⟩
  · rw [← he]
    exact hfi.2
  · rw [← he,← hfb]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)


lemma primeLog_factor_norm_le (w : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    {a : Eisenstein} (ha : primary a) (hw : ‖w a‖ ≤ M) :
    ‖(normalizedVonMangoldt a:ℂ)*w a‖ ≤ M ∧
    ‖(primeIndicator a:ℂ)*w a‖ ≤ M := by
  constructor
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (normalizedVonMangoldt_nonneg ha)]
    exact (mul_le_mul (normalizedVonMangoldt_le_one ha) hw (_root_.norm_nonneg _) zero_le_one).trans_eq
      (one_mul M)
  · by_cases hp : Prime a
    · simpa only [primeIndicator,ite_eq_left hp,Complex.ofReal_one,one_mul] using hw
    · simp only [primeIndicator,ite_eq_right hp,Complex.ofReal_zero,zero_mul,norm_zero]
      exact hM

/-- A divisor bound gives the genuine error coefficient a subpower amplitude. -/
theorem primeLogConvolutionError_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) → 1 ≤ Y →
      ∀ b ∈ orderedConvolutionSupport S, norm b ≤ Y →
      ‖primeLogConvolutionError S w b‖ ≤ C*Y^ε*(∏ i, M i) := by
  obtain ⟨C,hC,hfiber⟩ := primary_tuple_fiber_small_power (ι := ι) hε
  refine ⟨2*C,by positivity,?_⟩
  intro S w M Y hS hM hw hY b hb hbY
  have hMp : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  have ht (f : ι → Eisenstein) (hf : f ∈ Fintype.piFinset S) :
      ‖(∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i))-
        ∏ i, (primeIndicator (f i):ℂ)*w i (f i)‖ ≤ 2*∏ i, M i := by
    have hl (i : ι) := primeLog_factor_norm_le (w i) (hM i)
      (hS i (f i) (Fintype.mem_piFinset.mp hf i))
      (hw i (f i) (Fintype.mem_piFinset.mp hf i))
    have h1 : ‖∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i)‖ ≤ ∏ i, M i := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => _root_.norm_nonneg _) (fun i _ => (hl i).1)
    have h2 : ‖∏ i, (primeIndicator (f i):ℂ)*w i (f i)‖ ≤ ∏ i, M i := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => _root_.norm_nonneg _) (fun i _ => (hl i).2)
    exact (norm_sub_le _ _).trans (by linarith)
  rw [primeLogConvolutionError_sum]
  calc
    _ ≤ ∑ f ∈ (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b),
        ‖(∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i))-
          ∏ i, (primeIndicator (f i):ℂ)*w i (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b), 2*∏ i, M i :=
      Finset.sum_le_sum (fun f hf => ht f (Finset.mem_filter.mp hf).1)
    _ = (((Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)).card:ℝ)*(2*∏ i, M i) := by simp
    _ ≤ (C*Y^ε)*(2*∏ i, M i) :=
      mul_le_mul_of_nonneg_right (hfiber S hS Y hY b hb hbY) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

omit [Fintype ι] [DecidableEq ι] in
lemma coordinateSupport_lower (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y R : ℝ)
    (hW : ∀ i x, x < 1 → W i x = 0) (hX : ∀ i, 0 < X i)
    (hRX : ∀ i, R < X i) :
    ∀ i, ∀ n ∈ coordinateSupport W X Y i, primary n ∧ R < norm n := by
  intro i n hn
  obtain ⟨hn,hne⟩ := Finset.mem_filter.mp hn
  refine ⟨(mem_primaryElementBall.mp hn).1,(hRX i).trans_le ?_⟩
  have hlo : 1 ≤ norm n/X i := by
    by_contra h
    exact hne (hW i _ (lt_of_not_ge h))
  simpa only [one_mul] using (le_div_iff₀ (hX i)).mp hlo

omit [Fintype ι] [DecidableEq ι] in
lemma coordinateFactor_bound (q : ι → Eisenstein) (hq : ∀ i, q i ≠ 0)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (M : ι → ℝ)
    (hM : ∀ i x, ‖W i x‖ ≤ M i) (i : ι) (n : Eisenstein) :
    ‖coordinateFactor q η t W X i n‖ ≤ M i := by
  unfold coordinateFactor
  rw [norm_mul,norm_mul,mellinPhase_norm,mul_one]
  exact (mul_le_of_le_one_right (_root_.norm_nonneg _)
    (residueChar_norm_le_one (hq i) (η i) _)).trans (hM i _)

/-- Collection and support restriction are identities for arbitrary
coefficient functions; the prime and normalized prime cases specialize it. -/
lemma coordinate_convolution_collection (A : Eisenstein → ℂ)
    (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    (∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
      (∏ i, A (n i)*W i (norm (n i)/X i)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
          mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Y)) =
    ∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
      orderedConvolution (coordinateSupport W X Y)
        (fun i n => A n*coordinateFactor q η t W X i n) z*
        (mixedCubic a b z*V (norm z/Y)) := by
  rw [orderedConvolution_sum]
  let S : ι → Finset Eisenstein := fun _ => primaryElementBall (2*Y)
  let F : (ι → Eisenstein) → ℂ := fun n =>
    (∏ i, A (n i)*W i (norm (n i)/X i)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
        mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Y)
  have hsub : Fintype.piFinset (coordinateSupport W X Y) ⊆ Fintype.piFinset S := by
    intro n hn
    exact Fintype.mem_piFinset.mpr (fun i => (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hn i)).1)
  have he : (∑ n ∈ Fintype.piFinset (coordinateSupport W X Y), F n) =
      ∑ n ∈ Fintype.piFinset S, F n := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hex : ∃ i, W i (norm (n i)/X i) = 0 := by
      by_contra hh
      push Not at hh
      exact hnot (Fintype.mem_piFinset.mpr (fun i =>
        Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hn i,hh i⟩))
    obtain ⟨i,hi⟩ := hex
    dsimp [F]
    have hz : (∏ j, A (n j)*W j (norm (n j)/X j)*
      (mixedCubic a b (n j)*η j (Ideal.Quotient.mk (modulus (q j)) (n j))*
        mellinPhase (t j) (norm (n j)))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hi,mul_zero,zero_mul]
    rw [hz,zero_mul]
  change (∑ n ∈ Fintype.piFinset S, F n) = _
  rw [← he]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [F,coordinateFactor]
  rw [mixedCubic_prod _ _ ha hb,norm_finset_prod]
  rw [← mul_assoc,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateDifference
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact difference between normalized von Mangoldt tuples and
original prime-indicator tuples on the global smooth cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma coordinateProductCutoff_spec (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    coordinateProductCutoff W X Y ⊆ orderedConvolutionSupport (coordinateSupport W X Y) ∧
      ∀ b ∈ coordinateProductCutoff W X Y, norm b ≤ 2*Y :=
  ⟨Finset.filter_subset _ _,fun _ hb => (Finset.mem_filter.mp hb).2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIndicatorCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma orderedConvolution_primeIndicator (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (b : Eisenstein) :
    orderedConvolution S (fun i n => (primeIndicator n:ℂ)*w i n) b =
      orderedConvolution (fun i => (S i).filter Prime) w b := by
  unfold orderedConvolution
  let T := (Fintype.piFinset S).filter (fun n => (∏ i, n i) = b)
  let U := (Fintype.piFinset (fun i => (S i).filter Prime)).filter (fun n => (∏ i, n i) = b)
  have hsub : U ⊆ T := by
    intro n hn
    obtain ⟨hn,hprod⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i =>
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hn i)).1),hprod⟩
  have he : (∑ n ∈ U, ∏ i, (primeIndicator (n i):ℂ)*w i (n i)) =
      ∑ n ∈ T, ∏ i, (primeIndicator (n i):ℂ)*w i (n i) := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hex : ∃ i, ¬Prime (n i) := by
      by_contra h
      push Not at h
      have ht := Finset.mem_filter.mp hn
      exact hnot (Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr
        (fun i => Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp ht.1 i,h i⟩),ht.2⟩)
    obtain ⟨i,hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [primeIndicator,ite_eq_right hi,Complex.ofReal_zero,zero_mul]
  change (∑ n ∈ T, _) = ∑ n ∈ U, _
  rw [← he]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.prod_congr rfl
  intro i hi
  have hp := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hn).1 i)).2
  simp only [primeIndicator,ite_eq_left hp,Complex.ofReal_one,one_mul]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinatePrimeSupport_primary (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    ∀ i, ∀ p ∈ coordinatePrimeSupport W X Y i, primaryPrime p := by
  intro i p hp
  exact ⟨coordinateSupport_primary W X Y i p (Finset.mem_filter.mp hp).1,
    (Finset.mem_filter.mp hp).2⟩

lemma coordinatePrimeCutoff_spec (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    coordinatePrimeCutoff W X Y ⊆ orderedConvolutionSupport (coordinatePrimeSupport W X Y) ∧
      ∀ b ∈ coordinatePrimeCutoff W X Y, norm b ≤ 2*Y :=
  ⟨Finset.filter_subset _ _,fun _ hb => (Finset.mem_filter.mp hb).2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeTwists
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact multiplicative twists of the manuscript's squarefree prime coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedConvolution_mul_character (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (χ : Eisenstein →* ℂ) (z : Eisenstein) :
    orderedConvolution S (fun i n => w i n*χ n) z = orderedConvolution S w z*χ z := by
  unfold orderedConvolution
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.prod_mul_distrib,← map_prod, (Finset.mem_filter.mp hn).2]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeCoordinateCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of angular coordinate tuples. The same fixed theta
factor occurs on each original coordinate and hence on their product. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma angular_coordinate_convolution_collection (ℓ : ℤ) (A : Eisenstein → ℂ)
    (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    primaryAngularCoefficientTuple ℓ A a b q η t W X V Y =
      ∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
        orderedConvolution (coordinateSupport W X Y)
          (fun i n => A n*coordinateFactor q η t W X i n) z*
            (mixedCubic a b z*theta ℓ z*V (norm z/Y)) := by
  let χ : Eisenstein →* ℂ :=
    { toFun := theta ℓ, map_one' := theta_one ℓ, map_mul' := theta_mul ℓ }
  have he : primaryAngularCoefficientTuple ℓ A a b q η t W X V Y =
      ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        (∏ i, (A (n i)*χ (n i))*W i (norm (n i)/X i)*
          (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
            mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Y) := by
    unfold primaryAngularCoefficientTuple
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp only [χ, MonoidHom.coe_mk, OneHom.coe_mk]
    ring
  rw [he,coordinate_convolution_collection (fun n => A n*χ n) a b ha hb q η t W X V Y]
  apply Finset.sum_congr rfl
  intro z _
  have hw : (fun i n => (A n*χ n)*coordinateFactor q η t W X i n) =
      (fun i n => (A n*coordinateFactor q η t W X i n)*χ n) := by
    funext i n
    ring
  rw [hw,orderedConvolution_mul_character]
  change (_*theta ℓ z)*_ = _
  ring

lemma angular_normalized_prime_tuple_difference (ℓ : ℤ) (a b : Eisenstein)
    (ha : primary a) (hb : primary b) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryAngularCoefficientTuple ℓ (fun n => (normalizedVonMangoldt n:ℂ)) a b q η t W X V Y-
      primaryAngularPrimeIndicatorTuple ℓ a b q η t W X V Y =
        angularPrimeCoordinateError ℓ a b q η t W X V Y := by
  rw [primaryAngularPrimeIndicatorTuple,
    angular_coordinate_convolution_collection ℓ _ a b ha hb,
    angular_coordinate_convolution_collection ℓ _ a b ha hb,← Finset.sum_sub_distrib]
  have he : (∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
      (orderedConvolution (coordinateSupport W X Y)
        (fun i n => (normalizedVonMangoldt n:ℂ)*coordinateFactor q η t W X i n) z*
          (mixedCubic a b z*theta ℓ z*V (norm z/Y))-
       orderedConvolution (coordinateSupport W X Y)
        (fun i n => (primeIndicator n:ℂ)*coordinateFactor q η t W X i n) z*
          (mixedCubic a b z*theta ℓ z*V (norm z/Y)))) =
      ∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
        primeLogConvolutionError (coordinateSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*theta ℓ z*V (norm z/Y)) := by
    apply Finset.sum_congr rfl
    intro z _
    unfold primeLogConvolutionError
    ring
  rw [he]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hnot
  have hlarge : 2*Y < norm z := lt_of_not_ge (fun h => hnot (Finset.mem_filter.mpr ⟨hz,h⟩))
  have hv := hV (norm z/Y) ((lt_div_iff₀ hY).mpr hlarge)
  simp only [hv,mul_zero]

lemma angular_primeIndicatorTuple_eq_prime_convolution (ℓ : ℤ) (a b : Eisenstein)
    (ha : primary a) (hb : primary b) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    primaryAngularPrimeIndicatorTuple ℓ a b q η t W X V Y =
      ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Y),
        orderedConvolution (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*theta ℓ z*V (norm z/Y)) := by
  rw [primaryAngularPrimeIndicatorTuple,angular_coordinate_convolution_collection ℓ _ a b ha hb]
  simp_rw [orderedConvolution_primeIndicator]
  symm
  apply Finset.sum_subset
  · intro z hz
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨n,Fintype.mem_piFinset.mpr (fun i =>
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hn i)).1),rfl⟩
  · intro z _ hnot
    rw [orderedConvolution_eq_zero_of_not_mem _ _ hnot,zero_mul]

lemma angular_primeIndicator_sub_squarefree_cutoff (ℓ : ℤ) (a b : Eisenstein)
    (ha : primary a) (hb : primary b) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryAngularPrimeIndicatorTuple ℓ a b q η t W X V Y-
      primaryAngularSquarefreePrimeTuple ℓ a b q η t W X V Y =
        angularSquarefreeCoordinateError ℓ a b q η t W X V Y := by
  rw [angular_primeIndicatorTuple_eq_prime_convolution ℓ a b ha hb]
  unfold primaryAngularSquarefreePrimeTuple angularSquarefreeCoordinateError
  rw [← Finset.sum_sub_distrib]
  simp only [squarefreeConvolutionError,sub_mul]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hnot
  have hlarge : 2*Y < norm z := lt_of_not_ge (fun h => hnot (Finset.mem_filter.mpr ⟨hz,h⟩))
  have hv := hV (norm z/Y) ((lt_div_iff₀ hY).mpr hlarge)
  simp only [hv,mul_zero,sub_self]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideLogDenominator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quadratic coordinate range accommodates the fixed dilations in
an output norm partition. The denominator identities need no upper range. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

lemma wideLogWeightParameters_mem {c Y X : ℝ} (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y)
    (hlo : Y^c ≤ X) (hhi : X ≤ Y^2) :
    (Real.log X/Real.log Y,1/Real.log Y) ∈ wideLogWeightParameters c := by
  have hlogY : 0 < Real.log Y := by linarith
  have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
  refine ⟨⟨?_,?_⟩,⟨by positivity,?_⟩⟩
  · apply (le_div_iff₀ hlogY).mpr
    have h := Real.log_le_log (Real.rpow_pos_of_pos hY0 c) hlo
    rw [Real.log_rpow hY0] at h
    nlinarith
  · apply (div_le_iff₀ hlogY).mpr
    have h := Real.log_le_log hX hhi
    rw [Real.log_pow] at h
    norm_num at h ⊢
    linarith
  · exact (one_div_le_one_div_of_le (by norm_num) hY).trans_eq (by norm_num)

lemma logDenominatorWeight_scale_lower {c Y X x : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (hlo : Y^c ≤ X) (hx : 1 ≤ x)
    (w : ℝ → ℂ) :
    logDenominatorWeight c w (Real.log X/Real.log Y,1/Real.log Y) x =
      (Real.log Y:ℂ)*w x/(Real.log (X*x):ℂ) := by
  have hlogY : 0 < Real.log Y := by linarith
  have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
  have hp : c ≤ Real.log X/Real.log Y := by
    apply (le_div_iff₀ hlogY).mpr
    have h := Real.log_le_log (Real.rpow_pos_of_pos hY0 c) hlo
    rw [Real.log_rpow hY0] at h
    linarith
  have hx0 : 0 < x := by linarith
  rw [logDenominatorWeight_eq hc w hp (by positivity) hx,Real.log_mul hX.ne' hx0.ne']
  push_cast
  have hCY : (Real.log Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogY.ne'
  field_simp

lemma normalizedVonMangoldt_weight_lower {c Y X : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (hlo : Y^c ≤ X)
    (w : ℝ → ℂ) (hw : ∀ x, x < 1 → w x = 0) (a : Eisenstein) :
    (normalizedVonMangoldt a:ℂ)*w (norm a/X) =
      (1/(Real.log Y:ℂ))*((MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt:ℝ):ℂ)*
        logDenominatorWeight c w (Real.log X/Real.log Y,1/Real.log Y) (norm a/X) := by
  by_cases hx : 1 ≤ norm a/X
  · have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
    rw [logDenominatorWeight_scale_lower hc hY0 hY hlo hx]
    have he : X*(norm a/X) = norm a := by field_simp
    rw [he]
    unfold normalizedVonMangoldt
    push_cast
    have hCY : (Real.log Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith))
    field_simp
  · have hz := hw _ (lt_of_not_ge hx)
    simp only [hz,mul_zero,logDenominatorWeight]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularWideLogDenominator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primaryAngularNormalizedVonMangoldtTuple_eq_lower {c Y : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ)
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hXlo : ∀ i, Y^c ≤ X i) :
    primaryAngularNormalizedVonMangoldtTuple ℓ a b q η t W X V Y =
      (1/(Real.log Y:ℂ))^(Fintype.card ι)*
      primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt)
        a b q η t (fun i => logDenominatorWeight c (W i)
          (Real.log (X i)/Real.log Y,1/Real.log Y)) X V Y := by
  unfold primaryAngularNormalizedVonMangoldtTuple primaryAngularCoefficientTuple primaryAngularCoordinateWeightedTuple primaryAngularTupleCore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp_rw [normalizedVonMangoldt_weight_lower hc hY0 hY (hXlo _) _ (hWlo _)]
  have he (i : ι) :
      1/(Real.log Y:ℂ)*((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        logDenominatorWeight c (W i) (Real.log (X i)/Real.log Y,1/Real.log Y) (norm (n i)/X i)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*theta ℓ (n i)*
          mellinPhase (t i) (norm (n i))) =
      (1/(Real.log Y:ℂ))*
        (((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*theta ℓ (n i)*
          mellinPhase (t i) (norm (n i))))*
        logDenominatorWeight c (W i) (Real.log (X i)/Real.log Y,1/Real.log Y) (norm (n i)/X i) := by ring
  simp_rw [he,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  ring

lemma angular_normalizedCoordinate_norm_le_lower {c Y : ℝ} (hc : 0 < c) (hY0 : 0 < Y)
    (hY : 1 ≤ Real.log Y) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ)
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hXlo : ∀ i, Y^c ≤ X i) :
    ‖primaryAngularNormalizedVonMangoldtTuple ℓ a b q η t W X V Y‖ ≤
      ‖primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt)
        a b q η t (fun i => logDenominatorWeight c (W i)
          (Real.log (X i)/Real.log Y,1/Real.log Y)) X V Y‖ := by
  rw [primaryAngularNormalizedVonMangoldtTuple_eq_lower ℓ hc hY0 hY a b q η t W X V hWlo hXlo,
    norm_mul,norm_pow]
  apply mul_le_of_le_one_left (_root_.norm_nonneg _)
  apply pow_le_one₀ (_root_.norm_nonneg _) _
  rw [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
  exact (div_le_one (by linarith)).mpr hY

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularCommonNormalizedExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both normalized prime moments uniformly over actual smooth-weight families. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem angular_balanced_common_normalized_exponents (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → 0 < Y → 1 ≤ Real.log Y →
      (∀ i, Y^c ≤ X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryAngularNormalizedVonMangoldtTuple ℓ a.1 a.2 q η t (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,e,he,hraw⟩ := angular_balanced_common_coordinate_exponents ℓ
    (γ := γ × (ι → wideLogWeightParameters c)) (ι := ι) hpub hHuxley V hV hposV hsmV hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,e,he,?_⟩
  intro W hW hWlo
  let L : (γ × (ι → wideLogWeightParameters c)) → ι → ℝ → ℂ :=
    fun r i => logDenominatorWeight c (W r.1 i) (r.2 i)
  have hL : UniformLogWeights (fun z : (γ × (ι → wideLogWeightParameters c)) × ι => L z.1 z.2) :=
    uniformCoordinateWideLogDenominatorWeights hc hW
  obtain ⟨T,hfamily⟩ := hraw L hL
  refine ⟨T,?_⟩
  intro r Y X q η t P hYT hY0 hlog hXlo hXhi hq hη hqY ht hP
  let p : ι → wideLogWeightParameters c := fun i =>
    ⟨(Real.log (X i)/Real.log Y,1/Real.log Y),wideLogWeightParameters_mem hY0 hlog (hXlo i) (hXhi i)⟩
  have hb := hfamily (r,p) Y X q η t P hYT
    (fun i => (Real.rpow_pos_of_pos hY0 c).trans_le (hXlo i)) hq hη hqY ht hP
  apply le_trans _ hb
  apply Finset.sum_le_sum
  intro a ha
  exact pow_le_pow_left₀ (_root_.norm_nonneg _)
    (angular_normalizedCoordinate_norm_le_lower ℓ hc hY0 hlog a.1 a.2 q η t (W r) X V (hWlo r) hXlo) 2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimarySparseMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse coefficient energy in the balanced conductor region. The pair
multiplicity is bounded using actual primary divisors, with no restriction
on the number of prime bases. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_pair_fiber_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Finset Eisenstein) (Y : ℝ), 1 ≤ Y →
      (∀ b ∈ B, primary b ∧ norm b ≤ Y) → ∀ n ∈ productSupport B,
      (((B.product B).filter (fun z => z.1*z.2 = n)).card:ℝ) ≤ C*Y^ε := by
  obtain ⟨C,hC,hbound⟩ := primary_divisor_card_small_power
    (show 0 < ε/2 by positivity)
  refine ⟨C,hC,?_⟩
  intro B Y hY hB n hn
  obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_image.mp hn
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
  have hn0 : n ≠ 0 := by
    rw [← he]
    exact mul_ne_zero (primary_ne_zero (hB a ha).1) (primary_ne_zero (hB b hb).1)
  have hnN : norm n ≤ Y^2 := by
    rw [← he,norm_mul_eq,pow_two]
    exact mul_le_mul (hB a ha).2 (hB b hb).2 (norm_nonneg _) (by linarith)
  calc
    _ ≤ ((B.filter (fun a => a ∣ n)).card:ℝ) :=
      Nat.cast_le.mpr (primary_pair_fiber_le_divisors B (fun b hb => (hB b hb).1) n)
    _ ≤ C*norm n^(ε/2) := hbound B (fun b hb => (hB b hb).1) n hn0
    _ ≤ C*(Y^2)^(ε/2) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hnN (by positivity)) hC.le
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0 ≤ Y)]
      congr 2
      ring

theorem primary_mixed_fourth_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q Y : ℝ), 1 ≤ Q → 1 ≤ Y →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (B : Finset Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ b ∈ B, primary b ∧ norm b ≤ Y) → ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^4) ≤
        C*Q^ε*(Q^2+Y^2)*Y^ε*(∑ b ∈ B, ‖v b‖^2)^2 := by
  obtain ⟨C,hC,hfourth⟩ := ordinary_mixed_fourth_moment hHuxley hε
  obtain ⟨K,hK,hfiber⟩ := primary_pair_fiber_power hε
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro Q Y hQ hY P B hP hB v
  exact (hfourth Q Y hQ hY P B hP
    (fun b hb => ⟨primary_ne_zero (hB b hb).1,(hB b hb).2⟩)
    (K*Y^ε) (hfiber B Y hY hB) v).trans_eq (by ring)

private lemma balancedPrimary_power {Y θ C E m₂ m₄ : ℝ}
    (hY : 1 ≤ Y) (hθ : 0 < θ) (hC : 0 < C) (hE : 0 ≤ E) (hm₂ : 0 ≤ m₂)
    (hCS : m₂^2 ≤ (324*Y^(2/3+θ/8))*m₄)
    (hfourth : m₄ ≤ 2*C*Y^(4-15*θ/8)*E^2) :
    m₂ ≤ Real.sqrt (648*C)*Y^(7/3-θ/2)*E := by
  have hY0 : 0 < Y := by linarith
  have hp : Y^(2/3+θ/8)*Y^(4-15*θ/8) = Y^(14/3-7*θ/4) := by
    rw [← Real.rpow_add hY0]
    congr 1
    ring
  have hs : m₂^2 ≤ 648*C*Y^(14/3-θ)*E^2 := by
    calc
      _ ≤ (324*Y^(2/3+θ/8))*(2*C*Y^(4-15*θ/8)*E^2) :=
        hCS.trans (mul_le_mul_of_nonneg_left hfourth (by positivity))
      _ = 648*C*(Y^(2/3+θ/8)*Y^(4-15*θ/8))*E^2 := by ring
      _ = 648*C*Y^(14/3-7*θ/4)*E^2 := by rw [hp]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg E)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  apply (sq_le_sq₀ hm₂ (by positivity)).mp
  have hp₂ : (Y^(7/3-θ/2))^2 = Y^(14/3-θ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
    congr 1
    ring
  have he : (Real.sqrt (648*C)*Y^(7/3-θ/2)*E)^2 = 648*C*Y^(14/3-θ)*E^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),hp₂]
  exact hs.trans_eq he.symm

/-- The sparse coefficient energy and the primary divisor bound
suffice for the actual balanced mixed-character second moment. -/
theorem primary_balanced_sparse_moment
    (hHuxley : HuxleyAdditiveLargeSieve) {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y E : ℝ), 1 ≤ Y → 0 ≤ E →
      ∀ B : Finset Eisenstein,
      (∀ b ∈ B, primary b ∧ norm b ≤ Y) →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧
        norm p.1 ≤ Y^(1/3+θ/16) ∧ norm p.2 ≤ Y^(1/3+θ/16)) →
      ∀ v : Eisenstein → ℂ, (∑ b ∈ B, ‖v b‖^2) ≤ E*Y^(1-θ) →
      (∑ p ∈ P, ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^2) ≤
        C*Y^(7/3-θ/2)*E := by
  obtain ⟨C,hC,hfourth⟩ := primary_mixed_fourth_moment hHuxley
    (show 0 < θ/16 by positivity)
  refine ⟨Real.sqrt (648*C),Real.sqrt_pos.mpr (by positivity),?_⟩
  intro Y E hY hE B hB P hP v hv
  have hY0 : 0 < Y := by linarith
  have hq : 2/3+θ/8 ≤ 1 := by linarith
  have hQ : 1 ≤ Y^(2/3+θ/8) := Real.one_le_rpow hY (by positivity)
  have hpair : ∀ p ∈ P, PrimarySquarefreePair p ∧
      norm (pairConductor p) ≤ Y^(2/3+θ/8) := by
    intro p hp
    refine ⟨(hP p hp).1,?_⟩
    unfold pairConductor
    rw [norm_mul_eq]
    have h := mul_le_mul (hP p hp).2.1 (hP p hp).2.2 (norm_nonneg _) (by positivity)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [← Real.rpow_add hY0]
    congr 1
    ring
  have hcard : (P.card:ℝ) ≤ 324*Y^(2/3+θ/8) := by
    have h := balanced_pair_card P (by positivity : 0 ≤ Y^(1/3+θ/16))
      (fun p hp => ⟨(hP p hp).1.1,(hP p hp).1.2.1,(hP p hp).2⟩)
    have hp : (Y^(1/3+θ/16))^2 = Y^(2/3+θ/8) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
      congr 1
      ring
    exact h.trans_eq (by rw [hp])
  let f (p : Eisenstein × Eisenstein) := ∑ b ∈ B, v b*mixedCubic p.1 p.2 b
  have hCS : (∑ p ∈ P, ‖f p‖^2)^2 ≤
      (324*Y^(2/3+θ/8))*∑ p ∈ P, ‖f p‖^4 :=
    (second_moment_sq_le_card_fourth P f).trans (mul_le_mul_of_nonneg_right hcard
      (Finset.sum_nonneg (fun _ _ => pow_nonneg (_root_.norm_nonneg _) _)))
  have hf := hfourth (Y^(2/3+θ/8)) Y hQ hY P B hpair hB v
  have hw : (Y^(2/3+θ/8))^(θ/16) ≤ Y^(θ/16) := by
    rw [← Real.rpow_mul hY0.le]
    exact Real.rpow_le_rpow_of_exponent_le hY (by nlinarith)
  have hl : (Y^(2/3+θ/8))^2 ≤ Y^2 := by
    have hbase : Y^(2/3+θ/8) ≤ Y := by
      nth_rw 2 [← Real.rpow_one Y]
      exact Real.rpow_le_rpow_of_exponent_le hY hq
    exact pow_le_pow_left₀ (by positivity) hbase 2
  have he : (Y^(1-θ))^2 = Y^(2-2*θ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
    congr 1
    ring
  have hp : Y^(θ/16)*Y^(2:ℝ)*Y^(θ/16)*Y^(2-2*θ) = Y^(4-15*θ/8) := by
    rw [← Real.rpow_add hY0,← Real.rpow_add hY0,← Real.rpow_add hY0]
    congr 1
    ring
  have hfour : (∑ p ∈ P, ‖f p‖^4) ≤ 2*C*Y^(4-15*θ/8)*E^2 := by
    calc
      _ ≤ C*Y^(θ/16)*(2*Y^2)*Y^(θ/16)*(E*Y^(1-θ))^2 := by
        apply hf.trans
        gcongr
        linarith
      _ = 2*C*(Y^(θ/16)*Y^(2:ℝ)*Y^(θ/16)*Y^(2-2*θ))*E^2 := by
        rw [mul_pow,he,← Real.rpow_two Y]
        ring
      _ = _ := by rw [hp]
  exact balancedPrimary_power hY hθ hC hE
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hCS hfour

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogCutoffEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A power saving for the exact higher-prime-power replacement error.
Both the sparse support and the coefficient amplitude are proved. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primeLogConvolutionError_cutoff_energy {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ), 1 ≤ Y →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, primary a ∧ Y^c < norm a) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      (∑ b ∈ B, ‖primeLogConvolutionError S w b‖^2) ≤
        K*Y^(1-c/16)*(∏ i, M i)^2 := by
  obtain ⟨C,hC,hamp⟩ := primeLogConvolutionError_bound (ι := ι)
    (show 0 < c/32 by positivity)
  obtain ⟨D,hD,hcount⟩ := largePrimePowerSupport_card_bound
  refine ⟨D*C^2,by positivity,?_⟩
  intro S w M Y hY hM hS B hB hBY hw
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  let T := B.filter (fun b => primeLogConvolutionError S w b ≠ 0)
  have hsub : T ⊆ largePrimePowerSupport Y c := fun b hb =>
    primeLogConvolutionError_support_of_norm_le S w hS
      (hBY b (Finset.mem_filter.mp hb).1) (Finset.mem_filter.mp hb).2
  have hcard : (T.card:ℝ) ≤ D*Y^(1-c/8) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount Y c hYp)
  have hsum : (∑ b ∈ T, ‖primeLogConvolutionError S w b‖^2) =
      ∑ b ∈ B, ‖primeLogConvolutionError S w b‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hn
    have hz : primeLogConvolutionError S w b = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨hb,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)]
  rw [← hsum]
  have hMp : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  have he : Y^(1-c/8)*(Y^(c/32))^2 = Y^(1-c/16) := by
    rw [← Real.rpow_mul_natCast hYp.le,← Real.rpow_add hYp]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ∑ _b ∈ T, (C*Y^(c/32)*(∏ i, M i))^2 := by
      apply Finset.sum_le_sum
      intro b hb
      have hbB := (Finset.mem_filter.mp hb).1
      have hbS := hB hbB
      have hbY : norm b ≤ Y := hBY b hbB
      exact pow_le_pow_left₀ (_root_.norm_nonneg _)
        (hamp S w M Y (fun i a ha => (hS i a ha).1) hM hw hY b hbS hbY) 2
    _ = (T.card:ℝ)*(C*Y^(c/32)*(∏ i, M i))^2 := by simp
    _ ≤ (D*Y^(1-c/8))*(C*Y^(c/32)*(∏ i, M i))^2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = (D*C^2)*(Y^(1-c/8)*(Y^(c/32))^2)*(∏ i, M i)^2 := by ring
    _ = _ := by rw [he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogCutoffMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime-log replacement moments on the actual global norm cutoff. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem primeLogConvolution_balanced_cutoff_moment (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ), 1 ≤ Y →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, primary a ∧ Y^c < norm a) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(1/3+c/256) ∧
        norm p.2 ≤ Y^(1/3+c/256)) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ B, ‖χ b‖ ≤ 1) →
      (∑ p ∈ P, ‖∑ b ∈ B,
        (primeLogConvolutionError S w b*χ b)*mixedCubic p.1 p.2 b‖^2) ≤
        C*(∏ i, M i)^2*Y^(7/3-c/32) := by
  obtain ⟨C,hC,hbound⟩ := primary_balanced_sparse_moment hHuxley
    (show 0 < c/16 by positivity) (show c/16 ≤ 1 by linarith)
  obtain ⟨K,hK,henergy⟩ := primeLogConvolutionError_cutoff_energy (ι := ι) hc
  have h₁ : c/16/16 = c/256 := by ring
  have h₂ : c/16/2 = c/32 := by ring
  simp only [h₁,h₂] at hbound
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro S w M Y hY hM hS B hB hBY hw P hP χ hχ
  have hH : ∀ b ∈ B, primary b ∧ norm b ≤ Y := by
    intro b hb
    refine ⟨orderedPrimarySupport_primary S
      (fun i a ha => (hS i a ha).1) (hB hb),?_⟩
    exact hBY b hb
  have hE : (∑ b ∈ B,
      ‖primeLogConvolutionError S w b*χ b‖^2) ≤
      (K*(∏ i, M i)^2)*Y^(1-c/16) :=
    ((coefficient_twist_energy_le B
      (primeLogConvolutionError S w) χ hχ).trans
      (henergy S w M Y hY hM hS B hB hBY hw)).trans_eq (by ring)
  exact (hbound Y (K*(∏ i, M i)^2) hY (by positivity) B hH P hP
    (fun b => primeLogConvolutionError S w b*χ b) hE).trans_eq (by ring)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeCoordinateErrors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual angular replacement errors obey the unchanged sparse
moment estimates; theta is included in the bounded outer coefficient. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem balanced_angular_primeCoordinateError_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (W : ι → ℝ → ℂ) (M X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ), 1 ≤ Y →
      (∀ i, q i ≠ 0) → (∀ i, 0 ≤ M i) → (∀ i x, ‖W i x‖ ≤ M i) →
      (∀ i x, x < 1 → W i x = 0) → (∀ i, (2*Y)^c < X i) →
      (∀ x, ‖V x‖ ≤ 1) → ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ (2*Y)^(1/3+c/256) ∧
        norm a.2 ≤ (2*Y)^(1/3+c/256)) →
      (∑ a ∈ P, ‖angularPrimeCoordinateError ℓ a.1 a.2 q η t W X V Y‖^2) ≤
        C*(∏ i, M i)^2*(2*Y)^(7/3-c/32) := by
  obtain ⟨C,hC,hbound⟩ := primeLogConvolution_balanced_cutoff_moment (ι := ι) hHuxley hc hc₁
  refine ⟨C,hC,?_⟩
  intro ℓ q η t W M X V Y hY hq hM hW hWlo hX hV P hP
  have hYp : 0 < 2*Y := by linarith
  have hXpos : ∀ i, 0 < X i := fun i => (Real.rpow_pos_of_pos hYp c).trans (hX i)
  have hS := coordinateSupport_lower W X Y ((2*Y)^c) hWlo hXpos hX
  have hB := coordinateProductCutoff_spec W X Y
  have hχ (z : Eisenstein) (hz : z ∈ coordinateProductCutoff W X Y) :
      ‖theta ℓ z*V (norm z/Y)‖ ≤ 1 := by
    have hp := orderedPrimarySupport_primary (coordinateSupport W X Y)
        (coordinateSupport_primary W X Y) (hB.1 hz)
    rw [norm_mul,norm_theta (primary_ne_zero hp) ℓ,one_mul]
    exact hV _
  have hh := hbound (coordinateSupport W X Y) (coordinateFactor q η t W X) M (2*Y)
    (by linarith) hM hS (coordinateProductCutoff W X Y) hB.1 hB.2
    (fun i n _ => coordinateFactor_bound q hq η t W X M hW i n) P hP
    (fun z => theta ℓ z*V (norm z/Y)) hχ
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a ha
  congr 2
  apply Finset.sum_congr rfl
  intro z hz
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIndicatorPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary power margins used to return from a global cutoff at
2Y to the original exceptional conductor neighborhoods. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma balanced_prime_error_rows {Y κ c : ℝ} (hY : 1 ≤ Y) (hc : 0 < c)
    (hκ : κ ≤ c/256) (a : Eisenstein × Eisenstein)
    (ha : PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
      norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) :
    PrimarySquarefreePair a ∧ norm a.1 ≤ (2*Y)^(1/3+c/256) ∧
      norm a.2 ≤ (2*Y)^(1/3+c/256) := by
  have hp : Y^(1/3+κ) ≤ (2*Y)^(1/3+c/256) :=
    (Real.rpow_le_rpow_of_exponent_le hY (by linarith)).trans
      (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
  exact ⟨ha.1,ha.2.1.trans hp,ha.2.2.1.trans hp⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeIndicatorMomentTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact angular prime discrepancy transfers normalized prime
moments to the literal prime-indicator tuples. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma angular_primeIndicator_moment_transfer {ρ : Type*} (P : Finset ρ)
    (ℓ : ℤ) (a b : ρ → Eisenstein) (hab : ∀ r ∈ P, primary (a r) ∧ primary (b r))
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    (∑ r ∈ P, ‖primaryAngularPrimeIndicatorTuple ℓ (a r) (b r) q η t W X V Y‖^2) ≤
      2*(∑ r ∈ P, ‖primaryAngularCoefficientTuple ℓ
        (fun n => (normalizedVonMangoldt n:ℂ)) (a r) (b r) q η t W X V Y‖^2)+
      2*(∑ r ∈ P, ‖angularPrimeCoordinateError ℓ (a r) (b r) q η t W X V Y‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r hr
  apply norm_square_le_central_tail
  rw [norm_sub_rev,angular_normalized_prime_tuple_difference ℓ (a r) (b r)
    (hab r hr).1 (hab r hr).2 q η t W X V hY hV]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ExplicitMomentAbsorption
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit error exponents, independent of the coefficient-bound constants. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma absorb_prime_coordinate_error_explicit {e d C : ℝ} (he : 0 < e) (hd : 0 < d)
    (hC : 0 ≤ C) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ Y : ℝ, T ≤ Y →
      2*Y^(7/3-e)+2*C*(2*Y)^(7/3-d) ≤ Y^(7/3-min e d/2) := by
  let δ := min e d
  let K := 2+2*C*2^(7/3-d)
  have hδ : 0 < δ := lt_min he hd
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < δ/2 by positivity)).eventually_ge_atTop K)
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y hY
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have h₁ : Y^(7/3-e) ≤ Y^(7/3-δ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by dsimp [δ]; linarith [min_le_left e d])
  have h₂ : Y^(7/3-d) ≤ Y^(7/3-δ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by dsimp [δ]; linarith [min_le_right e d])
  calc
    _ = 2*Y^(7/3-e)+(2*C*2^(7/3-d))*Y^(7/3-d) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hYp.le]
      ring
    _ ≤ 2*Y^(7/3-δ)+(2*C*2^(7/3-d))*Y^(7/3-δ) := by gcongr
    _ = K*Y^(7/3-δ) := by dsimp [K]; ring
    _ ≤ Y^(δ/2)*Y^(7/3-δ) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularCommonPrimeIndicatorExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weight-independent exponents for uniform smooth families. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]


 theorem angular_balanced_common_prime_exponents (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hVnorm : ∀ x, ‖V x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → 1 ≤ Real.log Y →
      (∀ i, (2*Y)^c < X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryAngularPrimeIndicatorTuple ℓ a.1 a.2 q η t (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ₀,hκ₀,hκ₀hi,e,he,hfamily⟩ := angular_balanced_common_normalized_exponents ℓ (γ := γ) (ι := ι)
    hpub hHuxley hc V hV hposV hsmV hVlo hVhi hGI hGQ
  obtain ⟨C,hC,herr⟩ := balanced_angular_primeCoordinateError_moment (ι := ι) hHuxley hc hc₁
  let κ := min κ₀ (c/256)
  have hκ : 0 < κ := lt_min hκ₀ (by positivity)
  have hκle : κ ≤ κ₀ := min_le_left _ _
  have hκc : κ ≤ c/256 := min_le_right _ _
  refine ⟨κ,hκ,hκle.trans hκ₀hi,min e (c/32)/2,by positivity,?_⟩
  intro W hW hWlo
  obtain ⟨T₀,hnorm⟩ := hfamily W hW hWlo
  obtain ⟨K,hK,hbound⟩ := hW.norm_bound
  let M : ι → ℝ := fun _ => K
  have hM0 : ∀ i, 0 ≤ M i := fun _ => hK
  let E := C*(∏ i, M i)^2
  obtain ⟨T₁,hT₁,habs⟩ := absorb_prime_coordinate_error_explicit he
    (show 0 < c/32 by positivity) (show 0 ≤ E by dsimp [E]; positivity)
  refine ⟨max T₀ T₁,?_⟩
  intro r Y X q η t P hYT hlog hXlo hXhi hq hη hqY ht hP
  have hM : ∀ i x, ‖W r i x‖ ≤ M i := fun i x => hbound (r,i) x
  have hYT₀ : T₀ ≤ Y := (le_max_left _ _).trans hYT
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans hYT
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hNXlo : ∀ i, Y^c ≤ X i := fun i =>
    (Real.rpow_le_rpow hYp.le (by linarith : Y ≤ 2*Y) hc.le).trans (hXlo i).le
  have hP₀ : ∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ₀) ∧
      norm a.2 ≤ Y^(1/3+κ₀) ∧ Y^(1/1000:ℝ) ≤ norm a.1 := by
    intro a ha
    have hp : Y^(1/3+κ) ≤ Y^(1/3+κ₀) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    exact ⟨(hP a ha).1,(hP a ha).2.1.trans hp,(hP a ha).2.2.1.trans hp,(hP a ha).2.2.2⟩
  have hn := hnorm r Y X q η t P hYT₀ hYp hlog hNXlo hXhi hq hη hqY ht hP₀
  have hd := herr ℓ q η t (W r) M X V Y hY1 hq hM0 hM (hWlo r) hXlo hVnorm P
    (fun a ha => balanced_prime_error_rows hY1 hc hκc a (hP a ha))
  have hm := angular_primeIndicator_moment_transfer P ℓ Prod.fst Prod.snd
    (fun a ha => ⟨(hP a ha).1.1,(hP a ha).1.2.1⟩) q η t (W r) X V hYp hVhi
  calc
    _ ≤ 2*(∑ a ∈ P, ‖primaryAngularNormalizedVonMangoldtTuple ℓ a.1 a.2 q η t (W r) X V Y‖^2)+
        2*(∑ a ∈ P, ‖angularPrimeCoordinateError ℓ a.1 a.2 q η t (W r) X V Y‖^2) := hm
    _ ≤ 2*Y^(7/3-e)+2*E*(2*Y)^(7/3-c/32) := by dsimp [E]; linarith
    _ ≤ _ := habs Y hYT₁

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RepeatedPrimeCutoffEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated-prime energy on the actual global norm cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma convolutionError_mem_largeSquareSupport_of_norm
    (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ) (Y D : ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p)
    {b : Eisenstein} (hbY : norm b ≤ Y) (hb : squarefreeConvolutionError S w b ≠ 0) :
    b ∈ largeSquareSupport Y D := by
  have hns : ¬Squarefree b := by
    intro hs
    simp [squarefreeConvolutionError,squarefreeConvolution,hs] at hb
  have ho : orderedConvolution S w b ≠ 0 := by
    simpa only [squarefreeConvolutionError,squarefreeConvolution,ite_eq_right hns,sub_zero] using hb
  obtain ⟨f,hf,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero ho
  obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
  have hprime : ∀ i, primaryPrime (f i) :=
    fun i => (hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)).1
  have hnot : ¬Function.Injective f := by
    intro hi
    exact hns (hfb ▸ (squarefree_prime_tuple_iff f hprime).mpr hi)
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hnot
  have hdvd : (f i)^2 ∣ ∏ k, f k := by
    have h := Finset.prod_dvd_prod_of_subset ({i,j}:Finset ι) Finset.univ f
      (Finset.subset_univ _)
    simpa [hne,hij,pow_two] using h
  have hprod0 : (∏ i, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => (hprime i).2.ne_zero)
  apply Finset.mem_filter.mpr
  refine ⟨mem_nonzeroNormBall.mpr ⟨?_,?_⟩,f i,?_,?_⟩
  · exact hbY
  · exact hfb ▸ hprod0
  · exact (hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)).2
  · exact hfb ▸ hdvd

private theorem convolutionError_cutoff_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (Y D E : ℝ),
      0 ≤ Y → 0 < D → 0 ≤ E →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ b ∈ B, ‖squarefreeConvolutionError S w b‖ ≤ E) →
      (∑ b ∈ B, ‖squarefreeConvolutionError S w b‖^2) ≤
        C*Y*D^(-(1/2:ℝ))*E^2 := by
  obtain ⟨C,hC,hcount⟩ := largeSquareSupport_card_bound
  refine ⟨C,hC,?_⟩
  intro S w Y D E hY hD hE hS B hB hBY hbound
  let T := B.filter (fun b => squarefreeConvolutionError S w b ≠ 0)
  have hsub : T ⊆ largeSquareSupport Y D := by
    intro b hb
    exact convolutionError_mem_largeSquareSupport_of_norm S w Y D hS
      (hBY b (Finset.mem_filter.mp hb).1) (Finset.mem_filter.mp hb).2
  have hcard : (T.card:ℝ) ≤ C*Y*D^(-(1/2:ℝ)) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount Y D hY hD)
  have heq : (∑ b ∈ T, ‖squarefreeConvolutionError S w b‖^2) =
      ∑ b ∈ B, ‖squarefreeConvolutionError S w b‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hnot
    have hz : squarefreeConvolutionError S w b = 0 := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨hb,hn⟩)
    simp [hz]
  rw [← heq]
  calc
    _ ≤ ∑ _b ∈ T, E^2 := by
      apply Finset.sum_le_sum
      intro b hb
      exact pow_le_pow_left₀ (_root_.norm_nonneg _) (hbound b (Finset.mem_filter.mp hb).1) 2
    _ = (T.card:ℝ)*E^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg E)

theorem primeConvolutionError_cutoff_power_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y c : ℝ),
      0 < Y → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ Y^c < norm p) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) →
      (∑ b ∈ B, ‖squarefreeConvolutionError S w b‖^2) ≤
        C*Y^(1-c/2)*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by
  obtain ⟨C,hC,hbound⟩ := convolutionError_cutoff_energy_bound (ι := ι)
  refine ⟨C,hC,?_⟩
  intro S w M Y c hY hM hS B hB hBY hw
  have hA : 0 ≤ ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))
  have hh := hbound S w Y (Y^c) _ hY.le (Real.rpow_pos_of_pos hY _) hA
    hS B hB hBY (fun b _ => convolutionError_norm_bound S w M
      (fun i p hp => (hS i p hp).1) hM hw b)
  have he : C*Y*(Y^c)^(-(1/2:ℝ)) = C*Y^(1-c/2) := by
    rw [← Real.rpow_mul hY.le]
    nth_rw 1 [← Real.rpow_one Y]
    rw [mul_assoc,← Real.rpow_add hY]
    congr 2
    ring
  simpa only [he] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RepeatedPrimeCutoffMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The repeated-prime replacement moments on the actual global norm cutoff. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem repeatedPrime_balanced_cutoff_moment (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ), 1 ≤ Y →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, primaryPrime a ∧ Y^c < norm a) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(1/3+c/32) ∧
        norm p.2 ≤ Y^(1/3+c/32)) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ B, ‖χ b‖ ≤ 1) →
      (∑ p ∈ P, ‖∑ b ∈ B,
        (squarefreeConvolutionError S w b*χ b)*mixedCubic p.1 p.2 b‖^2) ≤
        C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2*Y^(7/3-c/4) := by
  obtain ⟨C,hC,hbound⟩ := primary_balanced_sparse_moment hHuxley
    (show 0 < c/2 by positivity) (show c/2 ≤ 1 by linarith)
  obtain ⟨K,hK,henergy⟩ := primeConvolutionError_cutoff_power_energy (ι := ι)
  have h₁ : c/2/16 = c/32 := by ring
  have h₂ : c/2/2 = c/4 := by ring
  simp only [h₁,h₂] at hbound
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro S w M Y hY hM hS B hB hBY hw P hP χ hχ
  have hH : ∀ b ∈ B, primary b ∧ norm b ≤ Y := by
    intro b hb
    refine ⟨orderedPrimarySupport_primary S
      (fun i a ha => (hS i a ha).1.1) (hB hb),?_⟩
    exact hBY b hb
  have hE : (∑ b ∈ B,
      ‖squarefreeConvolutionError S w b*χ b‖^2) ≤
      (K*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2)*Y^(1-c/2) :=
    ((coefficient_twist_energy_le B
      (squarefreeConvolutionError S w) χ hχ).trans
      (henergy S w M Y c (by linarith) hM hS B hB hBY hw)).trans_eq (by ring)
  exact (hbound Y (K*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2) hY (by positivity) B hH P hP
    (fun b => squarefreeConvolutionError S w b*χ b) hE).trans_eq (by ring)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSquarefreeCoordinateErrors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual angular replacement errors obey the unchanged sparse
moment estimates; theta is included in the bounded outer coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem balanced_angular_squarefreeCoordinateError_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (W : ι → ℝ → ℂ) (M X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ), 1 ≤ Y →
      (∀ i, q i ≠ 0) → (∀ i, 0 ≤ M i) → (∀ i x, ‖W i x‖ ≤ M i) →
      (∀ i x, x < 1 → W i x = 0) → (∀ i, (2*Y)^c < X i) →
      (∀ x, ‖V x‖ ≤ 1) → ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ (2*Y)^(1/3+c/32) ∧
        norm a.2 ≤ (2*Y)^(1/3+c/32)) →
      (∑ a ∈ P, ‖angularSquarefreeCoordinateError ℓ a.1 a.2 q η t W X V Y‖^2) ≤
        C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2*(2*Y)^(7/3-c/4) := by
  obtain ⟨C,hC,hbound⟩ := repeatedPrime_balanced_cutoff_moment (ι := ι) hHuxley hc hc₁
  refine ⟨C,hC,?_⟩
  intro ℓ q η t W M X V Y hY hq hM hW hWlo hX hV P hP
  have hYp : 0 < 2*Y := by linarith
  have hXpos : ∀ i, 0 < X i := fun i => (Real.rpow_pos_of_pos hYp c).trans (hX i)
  have hS : ∀ i, ∀ p ∈ coordinatePrimeSupport W X Y i,
      primaryPrime p ∧ (2*Y)^c < norm p := by
    intro i p hp
    exact ⟨coordinatePrimeSupport_primary W X Y i p hp,
      (coordinateSupport_lower W X Y ((2*Y)^c) hWlo hXpos hX i p
        (Finset.mem_filter.mp hp).1).2⟩
  have hB := coordinatePrimeCutoff_spec W X Y
  have hχ (z : Eisenstein) (hz : z ∈ coordinatePrimeCutoff W X Y) :
      ‖theta ℓ z*V (norm z/Y)‖ ≤ 1 := by
    have hp := orderedPrimarySupport_primary (coordinatePrimeSupport W X Y)
        (fun i p hp => (coordinatePrimeSupport_primary W X Y i p hp).1) (hB.1 hz)
    rw [norm_mul,norm_theta (primary_ne_zero hp) ℓ,one_mul]
    exact hV _
  have hh := hbound (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) M (2*Y)
    (by linarith) hM hS (coordinatePrimeCutoff W X Y) hB.1 hB.2
    (fun i n _ => coordinateFactor_bound q hq η t W X M hW i n) P hP
    (fun z => theta ℓ z*V (norm z/Y)) hχ
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a ha
  congr 2
  apply Finset.sum_congr rfl
  intro z hz
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeMomentTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact squarefree discrepancy transfers prime moments to
the squarefree coefficient in the manuscript. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma balanced_squarefree_error_rows {Y κ c : ℝ} (hY : 1 ≤ Y) (hc : 0 < c)
    (hκ : κ ≤ c/256) (a : Eisenstein × Eisenstein)
    (ha : PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
      norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) :
    PrimarySquarefreePair a ∧ norm a.1 ≤ (2*Y)^(1/3+c/32) ∧
      norm a.2 ≤ (2*Y)^(1/3+c/32) := by
  have hp := balanced_prime_error_rows hY hc hκ a ha
  have he : (2*Y)^(1/3+c/256) ≤ (2*Y)^(1/3+c/32) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  exact ⟨hp.1,hp.2.1.trans he,hp.2.2.trans he⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSquarefreeMomentTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact angular squarefree discrepancy transfers moments to the
squarefree prime coefficient, with the original product cutoff retained. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma angular_squarefreePrime_moment_transfer {ρ : Type*} (P : Finset ρ)
    (ℓ : ℤ) (a b : ρ → Eisenstein) (hab : ∀ r ∈ P, primary (a r) ∧ primary (b r))
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    (∑ r ∈ P, ‖primaryAngularSquarefreePrimeTuple ℓ (a r) (b r) q η t W X V Y‖^2) ≤
      2*(∑ r ∈ P, ‖primaryAngularPrimeIndicatorTuple ℓ (a r) (b r) q η t W X V Y‖^2)+
      2*(∑ r ∈ P, ‖angularSquarefreeCoordinateError ℓ (a r) (b r) q η t W X V Y‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r hr
  apply norm_square_le_central_tail
  rw [norm_sub_rev,angular_primeIndicator_sub_squarefree_cutoff ℓ (a r) (b r)
    (hab r hr).1 (hab r hr).2 q η t W X V hY hV]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularCommonSquarefreePrimeExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weight-independent exponents for uniform smooth families. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]


 theorem angular_balanced_common_squarefree_exponents_oai (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hVnorm : ∀ x, ‖V x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → 1 ≤ Real.log Y →
      (∀ i, (2*Y)^c < X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryAngularSquarefreePrimeTuple ℓ a.1 a.2 q η t (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ₀,hκ₀,hκ₀hi,e,he,hfamily⟩ := angular_balanced_common_prime_exponents ℓ (γ := γ) (ι := ι)
    hpub hHuxley hc hc₁ V hV hposV hsmV hVlo hVhi hVnorm hGI hGQ
  obtain ⟨C,hC,herr⟩ := balanced_angular_squarefreeCoordinateError_moment (ι := ι) hHuxley hc hc₁
  let κ := min κ₀ (c/256)
  have hκ : 0 < κ := lt_min hκ₀ (by positivity)
  have hκle : κ ≤ κ₀ := min_le_left _ _
  have hκc : κ ≤ c/256 := min_le_right _ _
  refine ⟨κ,hκ,hκle.trans hκ₀hi,min e (c/4)/2,by positivity,?_⟩
  intro W hW hWlo
  obtain ⟨T₀,hnorm⟩ := hfamily W hW hWlo
  obtain ⟨K,hK,hbound⟩ := hW.norm_bound
  let M : ι → ℝ := fun _ => K
  have hM0 : ∀ i, 0 ≤ M i := fun _ => hK
  let E := C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2
  obtain ⟨T₁,hT₁,habs⟩ := absorb_prime_coordinate_error_explicit he
    (show 0 < c/4 by positivity) (show 0 ≤ E by dsimp [E]; positivity)
  refine ⟨max T₀ T₁,?_⟩
  intro r Y X q η t P hYT hlog hXlo hXhi hq hη hqY ht hP
  have hM : ∀ i x, ‖W r i x‖ ≤ M i := fun i x => hbound (r,i) x
  have hYT₀ : T₀ ≤ Y := (le_max_left _ _).trans hYT
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans hYT
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hP₀ : ∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ₀) ∧
      norm a.2 ≤ Y^(1/3+κ₀) ∧ Y^(1/1000:ℝ) ≤ norm a.1 := by
    intro a ha
    have hp : Y^(1/3+κ) ≤ Y^(1/3+κ₀) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    exact ⟨(hP a ha).1,(hP a ha).2.1.trans hp,(hP a ha).2.2.1.trans hp,(hP a ha).2.2.2⟩
  have hn := hnorm r Y X q η t P hYT₀ hlog hXlo hXhi hq hη hqY ht hP₀
  have hd := herr ℓ q η t (W r) M X V Y hY1 hq hM0 hM (hWlo r) hXlo hVnorm P
    (fun a ha => balanced_squarefree_error_rows hY1 hc hκc a (hP a ha))
  have hm := angular_squarefreePrime_moment_transfer P ℓ Prod.fst Prod.snd
    (fun a ha => ⟨(hP a ha).1.1,(hP a ha).1.2.1⟩) q η t (W r) X V hYp hVhi
  calc
    _ ≤ 2*(∑ a ∈ P, ‖primaryAngularPrimeIndicatorTuple ℓ a.1 a.2 q η t (W r) X V Y‖^2)+
        2*(∑ a ∈ P, ‖angularSquarefreeCoordinateError ℓ a.1 a.2 q η t (W r) X V Y‖^2) := hm
    _ ≤ 2*Y^(7/3-e)+2*E*(2*Y)^(7/3-c/4) := by dsimp [E]; linarith
    _ ≤ _ := habs Y hYT₁

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CubicFirstMoment.angular_balanced_common_squarefree_exponents_oai.{u_1, u_2} := @OAI.CubicFirstMoment.angular_balanced_common_squarefree_exponents_oai.{u_1, u_2}
