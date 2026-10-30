-- Prove2me | solution 1 for OAI.CubicFirstMoment.ordinary_stopped_low_kernel_bound_actual
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:42:23.65031+00:00
-- url     : https://prove2.me/submissions/9818bb7e-75bc-40af-96f6-a61de5d5414a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015
import Definitions.Def_OAIQ096A016
import Theorems.Thm_OAI_CubicFirstMoment_low_localized_height_integral_bound
import Theorems.Thm_OAI_CubicFirstMoment_stopped_centered_bilinear_log_saving_actual

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_SieveMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_QuantitativeNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramMellinTwist
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conversion of the existing Poisson/Mellin kernel's Fourier
frequency to the norm heights used by the proved structured moments. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mellinPhase_add_height (u v x : ℝ) :
    mellinPhase (u+v) x = mellinPhase u x*mellinPhase v x := by
  unfold mellinPhase
  rw [show (((u+v)*Real.log x:ℝ):ℂ)*Complex.I =
    ((u*Real.log x:ℝ):ℂ)*Complex.I+((v*Real.log x:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_add]

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticBilinearMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightMeanSquare
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite spectral expansion of the height-averaged square.
The diagonal and every off-diagonal pair are retained. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma continuous_normTwist (b : Eisenstein) : Continuous (fun u : ℝ => normTwist u b) := by
  unfold normTwist
  fun_prop

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpHeightPartition
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth height windows with ratio 3/2. Their support lies in [T,2T]
in absolute value, exactly the range of the proved bilinear estimates.
The finite telescoping identity keeps the actual truncation multiplier. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma heightWindow_norm_le (T t : ℝ) : ‖heightWindow T t‖ ≤ 1 := by
  rw [heightWindow, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [heightPartitionBump.nonneg (x := t/((3/2)*T)),
    heightPartitionBump.le_one (x := t/((3/2)*T)),
    heightPartitionBump.nonneg (x := t/T), heightPartitionBump.le_one (x := t/T)]

lemma heightWindow_telescope (T t : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, heightWindow (T*(3/2:ℝ)^j) t) =
      ((heightPartitionBump (t/(T*(3/2:ℝ)^n)) - heightPartitionBump (t/T) : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have he : (3/2:ℝ)*(T*(3/2:ℝ)^n) = T*(3/2:ℝ)^(n+1) := by rw [pow_succ]; ring
    simp only [heightWindow, he, Complex.ofReal_sub]
    ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightBilinearValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal normalized height-integrated Gauss bilinear form. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma heightBilinearValue_eq_integral (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (h : ℝ → ℂ) (hi : Integrable h) (X₀ T : ℝ) :
    heightBilinearValue P S α β h X₀ T = (T:ℂ)⁻¹*
      ∫ t : ℝ, (h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
        ∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist t (a*b) := by
  unfold heightBilinearValue
  congr 1
  calc
    _ = ∑ q ∈ P.product S, (α q.1*β q.2*gauss (q.1*q.2))*
        heightFourierIntegral h (Real.log (norm (q.1*q.2))-Real.log X₀) :=
      (Finset.sum_product P S _).symm
    _ = ∫ t : ℝ, (h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
        ∑ q ∈ P.product S, α q.1*β q.2*gauss (q.1*q.2)*normTwist t (q.1*q.2) :=
      height_norm_polynomial_integral _ _ _ h hi _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      exact Finset.sum_product P S _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CorrectedBilinearScale
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformCoordinateWeights
attribute [-instance] _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CenteredProductMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation of the smooth total-product factor in a
centered bilinear Gauss sum. The norm height is shifted by the true Mellin
frequency, and absolute integrability follows from the smooth weight. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem centered_product_mellin (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (hA : ∀ a ∈ A, primary a) (hB : ∀ b ∈ B, primary b)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) (u : ℝ) :
    centeredProductSmoothed A B α β ℓ W X u =
      ∫ τ : ℝ, zeroLineMellinWeight W X τ*centeredProductPolynomial A B α β ℓ (u-τ) := by
  let c := fun a b => α a*β b*theta ℓ (a*b)*centeredGauss (a*b)*normTwist u (a*b)
  let f := fun a b τ => zeroLineMellinWeight W X τ*(c a b*mellinPhase (-τ) (norm (a*b)))
  have hp (a : Eisenstein) (ha : a ∈ A) (b : Eisenstein) (hb : b ∈ B) :
      0 < norm (a*b) := norm_pos_of_ne_zero
        (mul_ne_zero (primary_ne_zero (hA a ha)) (primary_ne_zero (hB b hb)))
  have hi (a : Eisenstein) (ha : a ∈ A) (b : Eisenstein) (hb : b ∈ B) :
      Integrable (f a b) := metaplectic_mellin_term_integrable W hW hpos hsm hX (hp a ha b hb) (c a b)
  calc
    _ = ∑ a ∈ A, ∑ b ∈ B, ∫ τ : ℝ, f a b τ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact metaplectic_mellin_term W hW hpos hsm hX (hp a ha b hb) (c a b)
    _ = ∫ τ : ℝ, ∑ a ∈ A, ∑ b ∈ B, f a b τ := by
      rw [integral_finsetSum A (fun a ha => integrable_finsetSum B (hi a ha))]
      apply Finset.sum_congr rfl
      intro a ha
      exact (integral_finsetSum B (hi a ha)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with τ
      simp only [centeredProductPolynomial,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [f,c]
      rw [sub_eq_add_neg,normTwist_eq_mellinPhase,normTwist_eq_mellinPhase,mellinPhase_add_height]
      ring

theorem centered_product_mellin_integrable (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X : ℝ} (hX : 0 < X) (u : ℝ) :
    Integrable (fun τ : ℝ => zeroLineMellinWeight W X τ*
      centeredProductPolynomial A B α β ℓ (u-τ)) := by
  apply (zeroLineMellinWeight_integrable W hW hpos hsm hX).mul_bdd
    (c := ∑ a ∈ A, ∑ b ∈ B, ‖α a*β b*theta ℓ (a*b)*centeredGauss (a*b)‖)
  · have hc : Continuous (fun τ : ℝ => centeredProductPolynomial A B α β ℓ (u-τ)) := by
      unfold centeredProductPolynomial normTwist
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards with τ
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro b _
    rw [norm_mul,norm_normTwist,mul_one]

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
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimeUpper
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeDivisorMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squarefree product coefficient of the literal stopped sides.
Its divisor bound is proved before collecting equal norms. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_pair_coefficient_bound (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hP : ∀ a ∈ P, primary a)
    (hα : ∀ a ∈ P, Squarefree a → ‖α a‖ ≤ L*(2:ℝ)^(primaryPrimeFactors a).card)
    (hβ : ∀ b ∈ B, ‖β b‖ ≤ M)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    ‖primaryPairCoefficient P B (fun p => α p.1*β p.2) n‖ ≤
      (L*M)*(4:ℝ)^(primaryPrimeFactors n).card := by
  have hf : ∀ p ∈ primaryPairFiber P B n,
      ‖α p.1*β p.2‖ ≤ (L*M)*(2:ℝ)^(primaryPrimeFactors n).card := by
    intro p hp
    have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have he := (Finset.mem_filter.mp hp).2
    have hd : p.1 ∣ n := ⟨p.2,he.symm⟩
    have hsf : Squarefree p.1 := fun x hx => hs x (hx.trans hd)
    have hcard := Finset.card_le_card
      (primaryPrimeFactors_subset_of_dvd (hP p.1 hmem.1) hn hd)
    have ha : ‖α p.1‖ ≤ L*(2:ℝ)^(primaryPrimeFactors n).card :=
      (hα p.1 hmem.1 hsf).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) hcard) hL)
    rw [norm_mul]
    calc
      _ ≤ (L*(2:ℝ)^(primaryPrimeFactors n).card)*M :=
        mul_le_mul ha (hβ p.2 hmem.2) (_root_.norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hb := primaryPairCoefficient_norm_le P B hP n _
    (show 0 ≤ (L*M)*(2:ℝ)^(primaryPrimeFactors n).card by positivity) hf
  have hc : ((P.filter (fun a => a ∣ n)).card:ℝ) ≤
      (2:ℝ)^(primaryPrimeFactors n).card := by
    exact_mod_cast primary_squarefree_divisor_card P hP hn hs
  apply hb.trans
  calc
    _ ≤ (2:ℝ)^(primaryPrimeFactors n).card*((L*M)*(2:ℝ)^(primaryPrimeFactors n).card) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (L*M)*((2:ℝ)^(primaryPrimeFactors n).card)^2 := by ring
    _ = _ := by
      rw [←pow_mul, Nat.mul_comm, pow_mul]
      norm_num

lemma stopped_pair_coefficient_bound (E U P B : Finset Eisenstein)
    (ψ : ℝ → ℝ) (w : ℝ) (remaining : Eisenstein → Prop)
    (β : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hE : ∀ e ∈ E, primary e) (hP : ∀ a ∈ P, primary a)
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (hβ : ∀ b ∈ B, ‖β b‖ ≤ M)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    ‖primaryPairCoefficient P B
      (fun p => stoppedAlpha E U ψ w remaining p.1*β p.2) n‖ ≤
      M*(4:ℝ)^(primaryPrimeFactors n).card := by
  apply (squarefree_pair_coefficient_bound P B _ β zero_le_one hM hP
    (fun a ha hsf => ?_) hβ hn hs).trans_eq (by rw [one_mul])
  simpa only [one_mul] using (stoppedAlpha_divisor_bound E U hE hψ w remaining a).trans
    (show ((E.filter (fun e => e ∣ a)).card:ℝ) ≤
      (2:ℝ)^(primaryPrimeFactors a).card by
        exact_mod_cast primary_squarefree_divisor_card E hE (hP a ha) hsf)

lemma squarefreePairSupport_primary (P B : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hB : ∀ b ∈ B, primary b)
    {n : Eisenstein} (hn : n ∈ squarefreePairSupport P B) :
    primary n ∧ Squarefree n := by
  obtain ⟨hn,hns⟩ := Finset.mem_filter.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hm := Finset.mem_product.mp hp
  exact ⟨primary_mul (hP p.1 hm.1) (hB p.2 hm.2),hns⟩

lemma squarefree_pair_sum (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (F : Eisenstein → ℂ) :
    (∑ n ∈ squarefreePairSupport P B,
      primaryPairCoefficient P B (fun p => α p.1*β p.2) n*F n) =
    ∑ a ∈ P, ∑ b ∈ B, if Squarefree (a*b) then α a*β b*F (a*b) else 0 := by
  calc
    _ = ∑ n ∈ primaryPairSupport P B,
        primaryPairCoefficient P B (fun p => α p.1*β p.2) n*
          (if Squarefree n then F n else 0) := by
      rw [squarefreePairSupport,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ = ∑ p ∈ P ×ˢ B, α p.1*β p.2*
        (if Squarefree (p.1*p.2) then F (p.1*p.2) else 0) :=
      primaryPairCoefficient_sum P B _ _
    _ = _ := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      split_ifs <;> simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightEndpointProfile
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed compact profile removes the reciprocal singularity. Dilating
this profile gives the normalized endpoint weights used in localization. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma heightWindow_dilation {T : ℝ} (hT : 0 < T) (t : ℝ) :
    heightWindow T t = heightWindow 1 (t/T) := by
  have he : t/((3/2)*T) = (t/T)/((3/2)*1)  := by field_simp [hT.ne']
  simp only [heightWindow, he, mul_one, div_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductProfile
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed Schwartz function localized in a genuine dyadic height window.
The normalized profile and its scaled second derivative decay like 1/T. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff Topology
namespace CubicFirstMoment

lemma schwartzHeightWindow_smooth (f : SchwartzMap ℝ ℂ) (T : ℝ) :
    ContDiff ℝ ∞ (schwartzHeightWindow f T) :=
  (contDiff_const.mul f.smooth').mul (heightWindow_smooth T)

lemma schwartzHeightWindow_zero (f : SchwartzMap ℝ ℂ) {T : ℝ} (hT : 0 < T)
    (t : ℝ) (ht : t ∉ dyadicHeightSupport T) : schwartzHeightWindow f T t = 0 := by
  simp only [schwartzHeightWindow,heightWindow_zero hT ht,mul_zero]

lemma schwartzHeightWindow_tsupport (f : SchwartzMap ℝ ℂ) {T : ℝ} (hT : 0 < T) :
    tsupport (schwartzHeightWindow f T) ⊆ dyadicHeightSupport T := by
  apply closure_minimal _ (isClosed_Icc.union isClosed_Icc)
  intro t ht
  by_contra hh
  exact ht (schwartzHeightWindow_zero f hT t hh)

lemma schwartzHeightWindow_compact (f : SchwartzMap ℝ ℂ) {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (schwartzHeightWindow f T) :=
  (isCompact_Icc.union isCompact_Icc).of_isClosed_subset isClosed_closure
    (schwartzHeightWindow_tsupport f hT)

lemma schwartzHeightWindow_derivatives (f : SchwartzMap ℝ ℂ) {T : ℝ} (hT : 0 < T) :
    Integrable (schwartzHeightWindow f T) ∧
    Differentiable ℝ (schwartzHeightWindow f T) ∧
    Integrable (deriv (schwartzHeightWindow f T)) ∧
    Differentiable ℝ (deriv (schwartzHeightWindow f T)) ∧
    Integrable (deriv (deriv (schwartzHeightWindow f T))) := by
  have hs := schwartzHeightWindow_smooth f T
  have hd := (contDiff_infty_iff_deriv.mp hs).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hc := schwartzHeightWindow_compact f hT
  exact ⟨hs.continuous.integrable_of_hasCompactSupport hc,
    hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),hd.continuous.integrable_of_hasCompactSupport hc.deriv,
    hd.differentiable (by simp),hdd.continuous.integrable_of_hasCompactSupport hc.deriv.deriv⟩

lemma schwartzHeightWindow_second_zero (f : SchwartzMap ℝ ℂ) {T : ℝ} (hT : 0 < T)
    (t : ℝ) (ht : t ∉ dyadicHeightSupport T) :
    deriv (deriv (schwartzHeightWindow f T)) t = 0 := by
  apply deriv_of_notMem_tsupport
  intro hh
  exact ht (schwartzHeightWindow_tsupport f hT (tsupport_deriv_subset hh))

lemma schwartzHeightWindow_norm_bound (f : SchwartzMap ℝ ℂ) {T : ℝ} (hT : 0 < T)
    (t : ℝ) :
    ‖schwartzHeightWindow f T t‖ ≤ SchwartzMap.seminorm ℝ 2 0 f/T := by
  by_cases ht : t ∈ dyadicHeightSupport T
  · have htl : T ≤ |t| := by
      rcases ht with ht | ht
      · exact ht.1.trans (le_abs_self t)
      · exact (by linarith [ht.2] : T ≤ -t).trans (neg_le_abs t)
    have hf := SchwartzMap.le_seminorm' ℝ 2 0 f t
    simp only [iteratedDeriv_zero] at hf
    have hb : T^2*‖f t‖ ≤ SchwartzMap.seminorm ℝ 2 0 f :=
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT.le htl 2) (_root_.norm_nonneg _)).trans hf
    rw [schwartzHeightWindow,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hT.le]
    apply (mul_le_mul_of_nonneg_left (heightWindow_norm_le T t) (by positivity : 0 ≤ T*‖f t‖)).trans
    rw [mul_one]
    apply (le_div_iff₀ hT).mpr
    nlinarith only [hb]
  · rw [schwartzHeightWindow_zero f hT t ht,norm_zero]
    exact div_nonneg (apply_nonneg _ _) hT.le

lemma heightWindow_iteratedDeriv_bound {T : ℝ} (hT : 0 < T) (i : ℕ) (t : ℝ) :
    ‖iteratedDeriv i (heightWindow T) t‖ ≤
      SchwartzMap.seminorm ℝ 0 i heightWindowSchwartz/T^i := by
  have he : heightWindow T = fun x => heightWindowSchwartz (T⁻¹*x) := by
    change heightWindow T = fun x => heightWindow 1 (T⁻¹*x)
    funext x
    simpa only [div_eq_mul_inv,mul_comm T⁻¹] using heightWindow_dilation hT x
  rw [he,iteratedDeriv_comp_const_smul (heightWindowSchwartz.smooth i),norm_smul,
    Real.norm_eq_abs,abs_pow,abs_inv,abs_of_pos hT]
  have hb := SchwartzMap.le_seminorm' ℝ 0 i heightWindowSchwartz (T⁻¹*t)
  simp only [pow_zero,one_mul] at hb
  apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (T⁻¹)^i)).trans_eq
  rw [inv_pow,div_eq_mul_inv,mul_comm]

lemma schwartz_derivative_on_height (f : SchwartzMap ℝ ℂ) {T t : ℝ}
    (hT : 0 < T) (ht : T ≤ |t|) (i : ℕ) :
    ‖iteratedDeriv i f t‖ ≤ SchwartzMap.seminorm ℝ (i+2) i f/T^(i+2) := by
  apply (le_div_iff₀ (pow_pos hT _)).mpr
  have hb := SchwartzMap.le_seminorm' ℝ (i+2) i f t
  calc
    _ = T^(i+2)*‖iteratedDeriv i f t‖ := by ring
    _ ≤ |t|^(i+2)*‖iteratedDeriv i f t‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT.le ht _) (_root_.norm_nonneg _)
    _ ≤ _ := hb

lemma schwartzHeightWindow_second_bound (f : SchwartzMap ℝ ℂ) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 0 < T → ∀ t : ℝ,
      ‖(T:ℂ)^2*deriv (deriv (schwartzHeightWindow f T)) t‖ ≤ K/T := by
  let Q := fun i : ℕ => ((2:ℕ).choose i:ℝ)*
    SchwartzMap.seminorm ℝ (i+2) i f*SchwartzMap.seminorm ℝ 0 (2-i) heightWindowSchwartz
  let K := 1+∑ i ∈ Finset.range 3, Q i
  have hQ : ∀ i, 0 ≤ Q i := fun i => by dsimp [Q]; positivity
  have hK : 0 < K := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range 3) => hQ i)
    dsimp only [K]
    linarith
  refine ⟨K,hK,?_⟩
  intro T hT t
  by_cases ht : t ∈ dyadicHeightSupport T
  · have htl : T ≤ |t| := by
      rcases ht with ht | ht
      · exact ht.1.trans (le_abs_self t)
      · exact (by linarith [ht.2] : T ≤ -t).trans (neg_le_abs t)
    let z := fun i : ℕ => ((2:ℕ).choose i:ℂ)*iteratedDeriv i f t*
      iteratedDeriv (2-i) (heightWindow T) t
    have hz (i : ℕ) (hi : i ∈ Finset.range 3) : T^3*‖z i‖ ≤ Q i/T := by
      have hi2 : i ≤ 2 := by have := Finset.mem_range.mp hi; omega
      have hf := schwartz_derivative_on_height f hT htl i
      have hw := heightWindow_iteratedDeriv_bound hT (2-i) t
      dsimp only [z]
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      calc
        _ ≤ T^3*(((2:ℕ).choose i:ℝ)*
            (SchwartzMap.seminorm ℝ (i+2) i f/T^(i+2))*
            (SchwartzMap.seminorm ℝ 0 (2-i) heightWindowSchwartz/T^(2-i))) := by
          gcongr
        _ = Q i/T := by
          dsimp only [Q]
          interval_cases i <;> norm_num <;> field_simp
    have he : schwartzHeightWindow f T = fun x => (T:ℂ)*(f x*heightWindow T x) := by
      funext x
      simp only [schwartzHeightWindow,mul_assoc]
    have hp := iteratedDeriv_mul (n := 2) (x := t) (f.smooth 2).contDiffAt
      ((heightWindow_smooth T).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    have hd : iteratedDeriv 2 (schwartzHeightWindow f T) t =
        (T:ℂ)*∑ i ∈ Finset.range 3, z i := by
      rw [he,iteratedDeriv_const_mul_field]
      change iteratedDeriv 2 (fun x => f x*heightWindow T x) t = _ at hp
      rw [hp]
    have hd' : deriv (deriv (schwartzHeightWindow f T)) t =
        (T:ℂ)*∑ i ∈ Finset.range 3, z i := by
      simpa only [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] using hd
    rw [hd',norm_mul,norm_pow,norm_mul,Complex.norm_real,Real.norm_of_nonneg hT.le]
    calc
      _ = T^3*‖∑ i ∈ Finset.range 3, z i‖ := by ring
      _ ≤ T^3*∑ i ∈ Finset.range 3, ‖z i‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = ∑ i ∈ Finset.range 3, T^3*‖z i‖ := by rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range 3, Q i/T := Finset.sum_le_sum hz
      _ = (∑ i ∈ Finset.range 3, Q i)/T := by rw [Finset.sum_div]
      _ ≤ K/T := div_le_div_of_nonneg_right (by dsimp [K]; linarith) hT.le
  · rw [schwartzHeightWindow_second_zero f hT t ht,mul_zero,norm_zero]
    positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowLogScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer logarithmic exponents for the low-height localization.
These inequalities let the cell width be chosen before the error saving. -/
noncomputable section
namespace CubicFirstMoment

lemma low_large_log {Z : ℝ} (hZ : (65536:ℝ)^2 ≤ Z) : 8 ≤ 1+Real.log Z := by
  have hz : (2:ℝ)^16 ≤ Z := by norm_num at *; linarith
  have hh := Real.log_le_log (by positivity : 0 < (2:ℝ)^16) hz
  rw [Real.log_pow] at hh
  have htwo := Real.log_two_gt_d9
  norm_num only [Nat.cast_ofNat] at hh
  linarith

lemma low_outer_log_root {A Z L : ℝ} (hA : 0 ≤ A) (hZ : 0 < Z) (hL : 0 < L)
    (a : ℕ) (hbound : A ≤ Z^2*L^(3*a)) :
    A^(1/3:ℝ) ≤ Z^(2/3:ℝ)*L^a := by
  have h := Real.rpow_le_rpow hA hbound (show (0:ℝ) ≤ 1/3 by norm_num)
  have hnum : (Z^2)^(1/3:ℝ) = Z^(2/3:ℝ) := by
    rw [←Real.rpow_natCast Z 2,←Real.rpow_mul hZ.le]
    norm_num
  have hden : (L^(3*a))^(1/3:ℝ) = L^a := by
    rw [←Real.rpow_natCast L (3*a),←Real.rpow_mul hL.le]
    push_cast
    rw [show (3*(a:ℝ))*(1/3:ℝ) = (a:ℝ) by ring,Real.rpow_natCast]
  rwa [Real.mul_rpow (sq_nonneg Z) (pow_nonneg hL.le _),hnum,hden] at h

lemma low_diagonal_log_scale {A Z L : ℝ} (hA : 0 < A) (hZ : 0 < Z) (hL : 0 < L)
    (k d a : ℕ) (hbound : A ≤ Z^2*L^(3*a)) :
    A*Z*L^d/L^(a+k+d) ≤ A^(2/3:ℝ)*Z^(5/3:ℝ)/L^k := by
  have hr := low_outer_log_root hA.le hZ hL a hbound
  have ha : A^(2/3:ℝ)*A^(1/3:ℝ) = A := by
    rw [←Real.rpow_add hA]
    norm_num
  have hz : Z*Z^(2/3:ℝ) = Z^(5/3:ℝ) := by
    nth_rw 1 [←Real.rpow_one Z]
    rw [←Real.rpow_add hZ]
    norm_num
  calc
    _ = A^(2/3:ℝ)*Z*A^(1/3:ℝ)*L^d/L^(a+k+d) := by
      rw [mul_right_comm (A^(2/3:ℝ)),ha]
    _ ≤ A^(2/3:ℝ)*Z*(Z^(2/3:ℝ)*L^a)*L^d/L^(a+k+d) := by gcongr
    _ = _ := by
      rw [pow_add,pow_add]
      field_simp
      rw [←hz]

lemma low_remainder_log_scale {L A Z M : ℝ} (hL : L ≠ 0)
    (d D k : ℕ) :
    (L^D)^4*((L^D)^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(D*(d+4)+k)) =
      M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^k := by
  rw [pow_add,←pow_mul,←pow_mul]
  rw [Nat.mul_add,pow_add]
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowLogRoot
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CubicFirstMoment

lemma low_diagonal_root_log_saving {A Z L Mα Mβ Ea Eb : ℝ}
    (hA : 0 < A) (hZ : 0 < Z) (hL : 0 < L)
    (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ) (ha : 0 ≤ Ea) (hb : 0 ≤ Eb)
    (j dα dβ a : ℕ) (hbound : A ≤ Z^2*L^(3*a))
    (hea : Ea ≤ Mα*A*L^dα) (heb : Eb ≤ Mβ*Z*L^dβ) :
    Real.sqrt (A/L^(a+2*j+dα+dβ))*Real.sqrt Ea*Real.sqrt Eb ≤
      Real.sqrt (Mα*Mβ)*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^j := by
  let J := L^(a+2*j+dα+dβ)
  let R := Real.sqrt (A/J)*Real.sqrt Ea*Real.sqrt Eb
  let V := (A/J)*Eb
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hsq : ‖(R:ℂ)‖^2 ≤ Ea*V := by
    rw [Complex.norm_real,Real.norm_of_nonneg hR]
    dsimp [R,V]
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ A/J),Real.sq_sqrt ha,Real.sq_sqrt hb]
    exact le_of_eq (by ring)
  have hmass : V ≤ Mβ*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(2*j+dα) := by
    calc
      V ≤ (A/J)*(Mβ*Z*L^dβ) := mul_le_mul_of_nonneg_left heb (by positivity)
      _ = Mβ*(A*Z*L^dβ/L^(a+(2*j+dα)+dβ)) := by dsimp [J]; ring
      _ ≤ Mβ*(A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(2*j+dα)) :=
        mul_le_mul_of_nonneg_left (low_diagonal_log_scale hA hZ hL (2*j+dα) dβ a hbound) hMβ
      _ = _ := by ring
  have hh := bilinear_error_log_saving hMα hMβ hA hZ hL j dα ha hV hsq hea hmass
  simpa only [Complex.norm_real,Real.norm_of_nonneg hR] using hh

lemma low_remainder_root_log_saving {A Z L Mα M Ea : ℝ}
    (hA : 0 < A) (hZ : 0 < Z) (hL : 0 < L)
    (hMα : 0 ≤ Mα) (ha : 0 ≤ Ea) (j dα d D : ℕ)
    (hea : Ea ≤ Mα*A*L^dα) :
    (L^D)^2*Real.sqrt ((L^D)^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(D*(d+4)+(2*j+dα)))*
      Real.sqrt Ea ≤ Real.sqrt (Mα*M^2)*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^j := by
  let Q := (L^D)^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(D*(d+4)+(2*j+dα))
  let R := (L^D)^2*Real.sqrt Q*Real.sqrt Ea
  let V := (L^D)^4*Q
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hsq : ‖(R:ℂ)‖^2 ≤ Ea*V := by
    rw [Complex.norm_real,Real.norm_of_nonneg hR]
    dsimp [R,V]
    rw [mul_pow,mul_pow,Real.sq_sqrt hQ,Real.sq_sqrt ha]
    exact le_of_eq (by ring)
  have hmass : V ≤ M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(2*j+dα) := by
    exact (low_remainder_log_scale hL.ne' d D (2*j+dα)).le
  have hh := bilinear_error_log_saving hMα (sq_nonneg M) hA hZ hL j dα ha hV hsq hea hmass
  simpa only [Complex.norm_real,Real.norm_of_nonneg hR] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowNormalized
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic cell width and height threshold for the low-height range. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem low_localized_integral_log_saving
    (hpnt : PrimaryPrimePNT)
    {C Mα Mβ M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ)
    (hM : 0 ≤ M) (j dα dβ a : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ T H : ℝ),
      (65536:ℝ)^2 ≤ Z →
      2*Z^(3/2:ℝ) ≤ A → A ≤ Z^2*(1+Real.log Z)^(3*a) → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ H →
      (∀ n ∈ P, primary n ∧ 1 ≤ norm n/A ∧ norm n/A ≤ 2) →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ Z/2 ≤ norm n ∧ norm n ≤ Z) →
      (∀ n ∈ S, ‖β n‖ ≤ M) →
      (∑ n ∈ P, ‖α n‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ n ∈ S, ‖β n‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
      Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
      (∀ t, ‖h t‖ ≤ H) → (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
      (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ H) →
      (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
      ‖heightBilinearValue P S α β h X₀ T‖ ≤
        K*H*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨d,hfamily⟩ := low_localized_height_integral_bound hpnt hMV hC hHuxley
  let D := a+2*(j+1)+dα+dβ
  let q := D*(d+4)+(2*(j+1)+dα)
  obtain ⟨K,Ct,hK,hbound⟩ := hfamily q
  let B := Real.sqrt (Mα*Mβ)+Real.sqrt (Mα*M^2)
  refine ⟨2*K*(B+1),Ct+2*D,by dsimp [B]; positivity,?_⟩
  intro P S α β Z A X₀ T H hZ hA hAu hX hT hH hP hS hβ hea heb h hi hd hi' hd' hi'' hh hs hh2 hs2
  have hL8 := low_large_log hZ
  let L := 1+Real.log Z
  let J := L^D
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hLp : 0 < L := by linarith
  have hZp : 0 < Z := by nlinarith
  have hAp : 0 < A := lt_of_lt_of_le (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  have hD1 : 1 ≤ D := by dsimp [D]; omega
  have hJ : 8 ≤ J := hL8.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 hD1)
  have hJ1 : 1 ≤ J := by linarith
  have hT0 : L^Ct ≤ T := (pow_le_pow_right₀ hL1 (by omega : Ct ≤ Ct+2*D)).trans hT
  have hTJ : J^2 ≤ T := by
    dsimp [J]
    rw [←pow_mul]
    exact (pow_le_pow_right₀ hL1 (by omega : D*2 ≤ Ct+2*D)).trans hT
  have hTp : 0 < T := (pow_pos hLp Ct).trans_le hT0
  have hJle : J ≤ T := (le_self_pow₀ hJ1 (by norm_num : 2 ≠ 0)).trans hTJ
  have hratio : J*(J/T)^2 ≤ 1 := by
    have h1 : J/T ≤ 1 := (div_le_one hTp).mpr hJle
    have h2 : J^2/T ≤ 1 := (div_le_one hTp).mpr hTJ
    have hm : (J/T)*(J^2/T) ≤ 1 := by
      calc
        _ ≤ 1*(J^2/T) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ 1 := by simpa using h2
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hdiag := low_diagonal_root_log_saving hAp hZp hLp hMα hMβ
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (j+1) dα dβ a hAu hea heb
  have herr := low_remainder_root_log_saving (M := M) hAp hZp hLp hMα
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (j+1) dα d D hea
  have hroot : Real.sqrt (A/J)*Real.sqrt (∑ n ∈ P, ‖α n‖^2)*Real.sqrt (∑ n ∈ S, ‖β n‖^2)+
      J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^q)*Real.sqrt (∑ n ∈ P, ‖α n‖^2) ≤
      B*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^j := by
    have hb := add_le_add hdiag herr
    have he : Real.sqrt (A/J)*Real.sqrt (∑ n ∈ P, ‖α n‖^2)*Real.sqrt (∑ n ∈ S, ‖β n‖^2)+
        J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^q)*Real.sqrt (∑ n ∈ P, ‖α n‖^2) ≤
        B*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^(j+1) := by
      convert hb using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [J,D,q,B,L]
      ring
    exact he.trans (div_le_div_of_nonneg_left (by dsimp [B]; positivity)
      (pow_pos hLp j) (pow_le_pow_right₀ hL1 (by omega : j ≤ j+1)))
  have hb := hbound J hJ P S α β Z A X₀ T M H hZ hA hX hT0 hM hH hP hS hβ
    h hi hd hi' hd' hi'' hh hs hh2 hs2
  apply hb.trans
  have hr := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ K*(1+J*(J/T)^2)*H by positivity)
  apply hr.trans
  have hc : K*(1+J*(J/T)^2)*B ≤ 2*K*(B+1) := by
    have hB : 0 ≤ B := by dsimp [B]; positivity
    nlinarith [mul_nonneg hK.le hB,mul_le_mul_of_nonneg_left hratio (mul_nonneg hK.le hB)]
  have hc' := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ H*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^j by positivity)
  first | (convert hc' using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hc'.trans (le_of_eq (by ring)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductGaussWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A whole signed Mellin-height window for a fixed Schwartz multiplier.
This is an application of the proved localized Gauss estimate, retaining
its coefficient energies and its lower length/height ranges. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem schwartz_gauss_window_log_saving
    (hpnt : PrimaryPrimePNT) {C Mα Mβ M : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ) (hM : 0 ≤ M)
    (j dα dβ a : ℕ) (f : SchwartzMap ℝ ℂ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (P B : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ T : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^2*(1+Real.log Z)^(3*a) → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ T →
      (∀ n ∈ P, primary n ∧ 1 ≤ norm n/A ∧ norm n/A ≤ 2) →
      (∀ n ∈ B, primary n ∧ Squarefree n ∧ Z/2 ≤ norm n ∧ norm n ≤ Z) →
      (∀ n ∈ B, ‖β n‖ ≤ M) →
      (∑ n ∈ P, ‖α n‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ n ∈ B, ‖β n‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ‖∫ t : ℝ, (f t*heightWindow T t)*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
        ∑ c ∈ P, ∑ b ∈ B, α c*β b*gauss (c*b)*normTwist t (c*b)‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(T*(1+Real.log Z)^j) := by
  obtain ⟨K₀,Ct,hK₀,hbound⟩ := low_localized_integral_log_saving hpnt hMV hC
    hHuxley hMα hMβ hM j dα dβ a
  obtain ⟨K₂,hK₂,hsecond⟩ := schwartzHeightWindow_second_bound f
  let D := 1+SchwartzMap.seminorm ℝ 2 0 f+K₂
  have hD : 0 < D := by dsimp [D]; have := apply_nonneg (SchwartzMap.seminorm ℝ 2 0) f; linarith
  refine ⟨K₀*D,Ct,mul_pos hK₀ hD,?_⟩
  intro P B α β Z A X₀ T hZ hA hAu hX₀ hT hP hB hβ hαE hβE
  have hZ1 : 1 ≤ Z := by nlinarith
  have hT0 : 0 < T := (pow_pos (by linarith [Real.log_nonneg hZ1]) Ct).trans_le hT
  let h := schwartzHeightWindow f T
  have hs := schwartzHeightWindow_derivatives f hT0
  have hn (t : ℝ) : ‖h t‖ ≤ D/T :=
    (schwartzHeightWindow_norm_bound f hT0 t).trans
      (div_le_div_of_nonneg_right (by dsimp [D]; linarith) hT0.le)
  have hn₂ (t : ℝ) : ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ D/T :=
    (hsecond T hT0 t).trans
      (div_le_div_of_nonneg_right (by dsimp [D]; have := apply_nonneg (SchwartzMap.seminorm ℝ 2 0) f; linarith) hT0.le)
  have hb := hbound P B α β Z A X₀ T (D/T) hZ hA hAu hX₀ hT (by positivity)
    hP hB hβ hαE hβE h hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 hn
    (schwartzHeightWindow_zero f hT0) hn₂ (schwartzHeightWindow_second_zero f hT0)
  have he : heightBilinearValue P B α β h X₀ T =
      ∫ t : ℝ, (f t*heightWindow T t)*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
        ∑ c ∈ P, ∑ b ∈ B, α c*β b*gauss (c*b)*normTwist t (c*b) := by
    rw [heightBilinearValue_eq_integral P B α β h hs.1,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [h,schwartzHeightWindow]
    have hc : (T:ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
    field_simp
  rw [he] at hb
  convert hb using 1 <;> first | rfl | ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductWindowSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact infinite summation of the smooth height windows. The full
complement is obtained by dominated convergence, without a frequency cutoff. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace CubicFirstMoment

theorem height_window_complement_bound (F : ℝ → ℂ) (hF : Integrable F)
    {S K : ℝ} (hS : 0 < S) (hK : 0 ≤ K)
    (hwindow : ∀ n : ℕ,
      ‖∫ t : ℝ, heightWindow (S*(3/2:ℝ)^n) t*F t‖ ≤ K/(S*(3/2:ℝ)^n)) :
    ‖∫ t : ℝ, (1-(heightPartitionBump (t/S):ℂ))*F t‖ ≤ 3*K/S := by
  let G := fun (n : ℕ) (t : ℝ) =>
    ((heightPartitionBump (t/(S*(3/2:ℝ)^n))-
      heightPartitionBump (t/S):ℝ):ℂ)*F t
  have hfactor (n : ℕ) (t : ℝ) :
      ‖((heightPartitionBump (t/(S*(3/2:ℝ)^n))-
        heightPartitionBump (t/S):ℝ):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_le]
    constructor <;> linarith [heightPartitionBump.nonneg (x := t/(S*(3/2:ℝ)^n)),
      heightPartitionBump.le_one (x := t/(S*(3/2:ℝ)^n)),
      heightPartitionBump.nonneg (x := t/S),heightPartitionBump.le_one (x := t/S)]
  have hconv : Tendsto (fun n => ∫ t : ℝ, G n t) atTop
      (𝓝 (∫ t : ℝ, (1-(heightPartitionBump (t/S):ℂ))*F t)) := by
    apply tendsto_integral_of_dominated_convergence (fun t => ‖F t‖)
    · intro n
      exact ((Complex.continuous_ofReal.comp
        ((heightPartitionBump.continuous.comp (continuous_id.div_const _)).sub
          (heightPartitionBump.continuous.comp (continuous_id.div_const _)))).aestronglyMeasurable).mul
        hF.aestronglyMeasurable
    · exact hF.norm
    · intro n
      filter_upwards with t
      exact (norm_mul _ _).le.trans (mul_le_of_le_one_left (_root_.norm_nonneg _) (hfactor n t))
    · filter_upwards with t
      have hp : Tendsto (fun n : ℕ => S*(3/2:ℝ)^n) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hS (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
      apply tendsto_const_nhds.congr'
      filter_upwards [hp.eventually (eventually_ge_atTop |t|)] with n hn
      have hd : 0 < S*(3/2:ℝ)^n := by positivity
      have hb : heightPartitionBump (t/(S*(3/2:ℝ)^n)) = 1 := by
        apply heightPartitionBump_one
        rw [abs_div,abs_of_pos hd]
        exact (div_le_one hd).mpr hn
      simp only [G,hb,Complex.ofReal_sub,Complex.ofReal_one]
  have hpartial (n : ℕ) : ‖∫ t : ℝ, G n t‖ ≤ 3*K/S := by
    have hi (j : ℕ) : Integrable (fun t => heightWindow (S*(3/2:ℝ)^j) t*F t) := by
      apply hF.bdd_mul
      · exact (heightWindow_smooth _).continuous.aestronglyMeasurable
      · exact Filter.Eventually.of_forall (heightWindow_norm_le _)
    have he : (∫ t : ℝ, G n t) =
        ∑ j ∈ Finset.range n, ∫ t : ℝ, heightWindow (S*(3/2:ℝ)^j) t*F t := by
      rw [←integral_finsetSum _ (fun j _ => hi j)]
      apply integral_congr_ae
      filter_upwards with t
      rw [←Finset.sum_mul,heightWindow_telescope]
    rw [he]
    apply (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hwindow j)).trans ?_)
    have hgeom : (∑ j ∈ Finset.range n, (2/3:ℝ)^j) ≤ 3 := by
      have hg := geom_sum_mul_neg (2/3:ℝ) n
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2/3) n]
    calc
      _ = (K/S)*(∑ j ∈ Finset.range n, (2/3:ℝ)^j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [div_eq_mul_inv (K) (S*(3/2:ℝ)^j),mul_inv_rev,←inv_pow]
        norm_num
        ring
      _ ≤ (K/S)*3 := mul_le_mul_of_nonneg_left hgeom (div_nonneg hK hS.le)
      _ = _ := by ring
  exact le_of_tendsto hconv.norm (Filter.Eventually.of_forall hpartial)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductGaussTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete smooth Mellin complement of the Gauss polynomial follows
from the actual localized estimates and convergent smooth-window summation. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem schwartz_gauss_complement_log_saving
    (hpnt : PrimaryPrimePNT) {C Mα Mβ M : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ) (hM : 0 ≤ M)
    (j dα dβ a : ℕ) (f : SchwartzMap ℝ ℂ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (P B : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ S : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^2*(1+Real.log Z)^(3*a) → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ S →
      (∀ n ∈ P, primary n ∧ 1 ≤ norm n/A ∧ norm n/A ≤ 2) →
      (∀ n ∈ B, primary n ∧ Squarefree n ∧ Z/2 ≤ norm n ∧ norm n ≤ Z) →
      (∀ n ∈ B, ‖β n‖ ≤ M) →
      (∑ n ∈ P, ‖α n‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ n ∈ B, ‖β n‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ‖∫ t : ℝ, (1-(heightPartitionBump (t/S):ℂ))*f t*
        Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
        ∑ c ∈ P, ∑ b ∈ B, α c*β b*gauss (c*b)*normTwist t (c*b)‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(S*(1+Real.log Z)^j) := by
  obtain ⟨K,Ct,hK,hbound⟩ := schwartz_gauss_window_log_saving hpnt hMV hC hHuxley
    hMα hMβ hM j dα dβ a f
  refine ⟨3*K,Ct,by positivity,?_⟩
  intro P B α β Z A X₀ S hZ hA hAu hX₀ hS hP hB hβ hαE hβE
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hS0 : 0 < S := (pow_pos hL Ct).trans_le hS
  have hAp : 0 < A := (by positivity : 0 < 2*Z^(3/2:ℝ)).trans_le hA
  let Q := fun t : ℝ => ∑ c ∈ P, ∑ b ∈ B, α c*β b*gauss (c*b)*normTwist t (c*b)
  let phase := fun t : ℝ => Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)
  let F := fun t : ℝ => f t*(phase t*Q t)
  have hi : Integrable F := by
    apply f.integrable.mul_bdd (c := ∑ c ∈ P, ∑ b ∈ B, ‖α c*β b*gauss (c*b)‖)
    · have hc : Continuous (fun t => phase t*Q t) := by
        have hq : Continuous Q := by
          dsimp only [Q]
          apply continuous_finsetSum
          intro c hc
          apply continuous_finsetSum
          intro b hb
          exact continuous_const.mul (continuous_normTwist (c*b))
        exact (show Continuous phase by dsimp only [phase]; fun_prop).mul hq
      exact hc.aestronglyMeasurable
    · filter_upwards with t
      rw [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
      dsimp only [Q]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro c hc
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul,norm_normTwist,mul_one]
  have hwindow (n : ℕ) :
      ‖∫ t : ℝ, heightWindow (S*(3/2:ℝ)^n) t*F t‖ ≤
        (K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j)/(S*(3/2:ℝ)^n) := by
    have ht : (1+Real.log Z)^Ct ≤ S*(3/2:ℝ)^n :=
      hS.trans (le_mul_of_one_le_right hS0.le (one_le_pow₀ (by norm_num)))
    have hh := hbound P B α β Z A X₀ (S*(3/2:ℝ)^n)
      hZ hA hAu hX₀ ht hP hB hβ hαE hβE
    have he : (fun t => heightWindow (S*(3/2:ℝ)^n) t*F t) =
        fun t => (f t*heightWindow (S*(3/2:ℝ)^n) t)*phase t*Q t := by
      funext t
      dsimp only [F]
      ring
    rw [he]
    convert hh using 1 <;> first | rfl | ring
  have hb := height_window_complement_bound F hi hS0
    (show 0 ≤ K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j by positivity) hwindow
  have he : (fun t => (1-(heightPartitionBump (t/S):ℂ))*F t) =
      fun t => (1-(heightPartitionBump (t/S):ℂ))*f t*phase t*Q t := by
    funext t
    dsimp only [F]
    ring
  rw [he] at hb
  convert hb using 1 <;> first | rfl | ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every fixed divisor moment on primary squarefree elements follows from
the finite Euler product and the already specified ordinary prime theorem. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_fixed_reciprocal_sum (q : ℝ) (hq : 0 ≤ q) (S U : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hU : ∀ b ∈ S, primaryPrimeFactors b ⊆ U) :
    (∑ b ∈ S, q^(primaryPrimeFactors b).card / norm b) ≤
      ∏ p ∈ U, (1+q/norm p) := by
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
    exact Finset.prod_nonneg (fun p _ => div_nonneg hq (norm_nonneg p))

lemma squarefree_fixed_sum_le_euler (q : ℝ) (hq : 0 ≤ q) (S : Finset Eisenstein) {X : ℝ}
    (hX : 0 ≤ X) (hS : ∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ X) :
    (∑ b ∈ S, q^(primaryPrimeFactors b).card) ≤
      X*Real.exp (q*∑ p ∈ primeCutoff X, (norm p)⁻¹) := by
  have hsub : ∀ b ∈ S, primaryPrimeFactors b ⊆ primeCutoff X := by
    intro b hb p hp
    have hprime := primaryPrimeFactor_spec (hS b hb).1 hp
    exact mem_primeCutoff.mpr ⟨hprime.1,
      (norm_le_of_dvd_nonzero (primary_ne_zero (hS b hb).1) hprime.2).trans (hS b hb).2.2⟩
  have hprod : (∏ p ∈ primeCutoff X, (1+q/norm p)) ≤
      Real.exp (q*∑ p ∈ primeCutoff X, (norm p)⁻¹) := by
    rw [Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      exact add_nonneg zero_le_one (div_nonneg hq (norm_nonneg p))
    · intro p hp
      simpa only [div_eq_mul_inv,add_comm] using Real.add_one_le_exp (q*(norm p)⁻¹)
  calc
    _ ≤ ∑ b ∈ S, X*(q^(primaryPrimeFactors b).card/norm b) := by
      apply Finset.sum_le_sum
      intro b hb
      have hb0 := norm_pos_of_ne_zero (primary_ne_zero (hS b hb).1)
      calc
        _ = norm b*(q^(primaryPrimeFactors b).card/norm b) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (hS b hb).2.2 (by positivity)
    _ = X*∑ b ∈ S, q^(primaryPrimeFactors b).card/norm b := by rw [Finset.mul_sum]
    _ ≤ X*(∏ p ∈ primeCutoff X, (1+q/norm p)) :=
      mul_le_mul_of_nonneg_left (squarefree_fixed_reciprocal_sum q hq S (primeCutoff X)
        (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩) hsub) hX
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod hX

theorem squarefree_fixed_divisor_moment (hpnt : PrimaryPrimePNT) (q : ℝ) (hq : 0 ≤ q) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (X : ℝ) (S : Finset Eisenstein),
      Real.exp 1 ≤ X →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ X) →
      (∑ b ∈ S, q^(primaryPrimeFactors b).card) ≤ K*X*(1+Real.log X)^d := by
  obtain ⟨C,hC,hprime⟩ := primaryPrime_reciprocal_exp_bound hpnt
  obtain ⟨d,hd⟩ := exists_nat_ge (q*C)
  refine ⟨Real.exp (q*C),d,Real.exp_pos _,?_⟩
  intro X S hX hS
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hl : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hl0 : 0 < Real.log X := zero_lt_one.trans_le hl
  have hrec := hprime (Real.log X) hl
  rw [Real.exp_log hX0] at hrec
  have he : Real.exp (q*(C*(1+Real.log (Real.log X)))) =
      Real.exp (q*C)*(Real.log X)^(q*C) := by
    rw [Real.rpow_def_of_pos hl0,←Real.exp_add]
    congr 1
    ring
  have hpow : (Real.log X)^(q*C) ≤ (1+Real.log X)^d := by
    calc
      _ ≤ (Real.log X)^(d:ℝ) := Real.rpow_le_rpow_of_exponent_le hl hd
      _ = (Real.log X)^d := Real.rpow_natCast _ _
      _ ≤ _ := pow_le_pow_left₀ hl0.le (by linarith : Real.log X ≤ 1+Real.log X) d
  calc
    _ ≤ X*Real.exp (q*∑ p ∈ primeCutoff X, (norm p)⁻¹) :=
      squarefree_fixed_sum_le_euler q hq S hX0.le hS
    _ ≤ X*Real.exp (q*(C*(1+Real.log (Real.log X)))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hrec hq)) hX0.le
    _ = X*(Real.exp (q*C)*(Real.log X)^(q*C)) := by rw [he]
    _ ≤ X*(Real.exp (q*C)*(1+Real.log X)^d) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)) hX0.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the product squarefree model and its ordinary
height mean for the actual stopped outer coefficient. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefreeProductModel_collection (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) :
    squarefreeProductModel P B α β u =
      dispersionModel (squarefreePairSupport P B)
        (primaryPairCoefficient P B (fun p => α p.1*β p.2)) u := by
  rw [dispersionModel]
  simpa only [squarefreeProductModel,mul_assoc] using
    (squarefree_pair_sum P B α β (fun n =>
      normTwist u n*((norm n^(-1/6:ℝ):ℝ):ℂ))).symm

lemma continuous_squarefreeProductModel (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) :
    Continuous (fun t => squarefreeProductModel P B α β (t+u)) := by
  unfold squarefreeProductModel
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  split_ifs
  · exact (continuous_const.mul ((continuous_normTwist (a*b)).comp
      (continuous_id.add continuous_const))).mul continuous_const
  · exact continuous_const

lemma centered_product_eq_gauss_sub_model (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) :
    centeredProductPolynomial P B α β 0 u =
      (∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*normTwist u (a*b))-
        (cStar:ℂ)*squarefreeProductModel P B α β u := by
  simp only [centeredProductPolynomial,theta_zero, mul_one,
    squarefreeProductModel,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [centeredGauss,idealMoebius_sq_complex]
  by_cases hs : Squarefree (a*b)
  · simp only [ite_eq_left hs]
    ring
  · simp only [ite_eq_right hs,mul_zero,zero_mul,sub_zero]

lemma divisor_model_norm_bound (S : Finset Eisenstein) (γ : Eisenstein → ℂ)
    {X M : ℝ} (hX : 0 < X) (hM : 0 ≤ M)
    (hS : ∀ n ∈ S, X ≤ norm n)
    (hγ : ∀ n ∈ S, ‖γ n‖ ≤ M*(4:ℝ)^(primaryPrimeFactors n).card) (u : ℝ) :
    ‖dispersionModel S γ u‖ ≤
      M*X^(-1/6:ℝ)*(∑ n ∈ S, (4:ℝ)^(primaryPrimeFactors n).card) := by
  unfold dispersionModel
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul,norm_mul,norm_normTwist,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg n) _)]
  calc
    _ ≤ (M*(4:ℝ)^(primaryPrimeFactors n).card)*X^(-1/6:ℝ) :=
      mul_le_mul (hγ n hn)
        (Real.rpow_le_rpow_of_nonpos hX (hS n hn) (by norm_num))
        (Real.rpow_nonneg (norm_nonneg n) _) (by positivity)
    _ = _ := by ring

theorem stopped_product_model_norm (hpnt : PrimaryPrimePNT) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (E U P B : Finset Eisenstein)
      (ψ : ℝ → ℝ) (w : ℝ) (remaining : Eisenstein → Prop)
      (β : Eisenstein → ℂ) (X Y M u : ℝ),
      (∀ e ∈ E, primary e) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      Real.exp 1 ≤ Y → 0 < X → 0 ≤ M →
      (∀ a ∈ P, primary a) → (∀ b ∈ B, primary b) →
      (∀ a ∈ P, ∀ b ∈ B, X ≤ norm (a*b) ∧ norm (a*b) ≤ Y) →
      (∀ b ∈ B, ‖β b‖ ≤ M) →
      ‖squarefreeProductModel P B (stoppedAlpha E U ψ w remaining) β u‖ ≤
        K*M*Y*X^(-1/6:ℝ)*(1+Real.log Y)^d := by
  obtain ⟨K,d,hK,hmoment⟩ := squarefree_fixed_divisor_moment hpnt 4 (by norm_num)
  refine ⟨K,d,hK,?_⟩
  intro E U P B ψ w remaining β X Y M u hE hψ hY hX hM hP hB hnorm hβ
  let S := squarefreePairSupport P B
  let γ := primaryPairCoefficient P B (fun p => stoppedAlpha E U ψ w remaining p.1*β p.2)
  have hS (n : Eisenstein) (hn : n ∈ S) :
      primary n ∧ Squarefree n ∧ X ≤ norm n ∧ norm n ≤ Y := by
    have hs := squarefreePairSupport_primary P B hP hB hn
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hn).1
    have hm := Finset.mem_product.mp hp
    exact ⟨hs.1,hs.2,he ▸ (hnorm p.1 hm.1 p.2 hm.2)⟩
  have hγ : ∀ n ∈ S, ‖γ n‖ ≤ M*(4:ℝ)^(primaryPrimeFactors n).card := by
    intro n hn
    exact stopped_pair_coefficient_bound E U P B ψ w remaining β hM hE hP hψ hβ
      (hS n hn).1 (hS n hn).2.1
  rw [squarefreeProductModel_collection]
  apply (divisor_model_norm_bound S γ hX hM (fun n hn => (hS n hn).2.2.1) hγ u).trans
  calc
    _ ≤ M*X^(-1/6:ℝ)*(K*Y*(1+Real.log Y)^d) :=
      mul_le_mul_of_nonneg_left (hmoment Y S hY
        (fun n hn => ⟨(hS n hn).1,(hS n hn).2.1,(hS n hn).2.2.2⟩)) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductMellinPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact phases in the product Mellin integral. The scale oscillation is
kept outside the fixed Schwartz profile, so its derivative cost is uniform. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma reflectedZeroMellinProfile_apply (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hpos : tsupport V ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ V) (t : ℝ) :
    reflectedZeroMellinProfile V hV hpos hsm t = zeroLineMellinWeight V 1 (-t) := by
  simp only [reflectedZeroMellinProfile,smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,LinearIsometryEquiv.coe_neg,
    mellinVerticalSchwartz_apply,Complex.ofReal_zero,zero_add,
    zeroLineMellinWeight,Complex.ofReal_one,Complex.one_cpow,mul_one,Complex.real_smul]

lemma zeroLineMellinWeight_reflected_phase (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hpos : tsupport V ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ V)
    {X : ℝ} (hX : 0 < X) (t : ℝ) :
    zeroLineMellinWeight V X (-t) = reflectedZeroMellinProfile V hV hpos hsm t*
      Complex.exp ((-Real.log X*t:ℝ)*Complex.I) := by
  rw [reflectedZeroMellinProfile_apply]
  simp only [zeroLineMellinWeight,Complex.ofReal_one,Complex.one_cpow,mul_one]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne'),
    ←Complex.ofReal_log hX.le]
  congr 1
  push_cast
  ring

lemma gaussProduct_shift (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (hP : ∀ a ∈ P, primary a) (hB : ∀ b ∈ B, primary b) (u t : ℝ) :
    (∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*normTwist (u+t) (a*b)) =
    ∑ a ∈ P, ∑ b ∈ B, (α a*normTwist u a)*(β b*normTwist u b)*
      gauss (a*b)*normTwist t (a*b) := by
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hsum : normTwist (u+t) (a*b) = normTwist u (a*b)*normTwist t (a*b) := by
    simpa only [normTwist_eq_mellinPhase] using mellinPhase_add_height u t (norm (a*b))
  rw [hsum,normTwist_mul u (primary_ne_zero (hP a ha)) (primary_ne_zero (hB b hb))]
  ring

lemma norm_twisted_coefficient (α : Eisenstein → ℂ) (u : ℝ) (a : Eisenstein) :
    ‖α a*normTwist u a‖ = ‖α a‖ := by
  rw [norm_mul,norm_normTwist,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductMellinSplit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact smooth splitting of the complete Mellin line, with elementary
central and model-complement bounds. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma height_bump_norm (S t : ℝ) : ‖(heightPartitionBump (t/S):ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg heightPartitionBump.nonneg] using
    (heightPartitionBump.le_one (x := t/S))

lemma height_bump_complement_norm (S t : ℝ) :
    ‖(1:ℂ)-(heightPartitionBump (t/S):ℂ)‖ ≤ 1 := by
  rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (sub_nonneg.mpr heightPartitionBump.le_one)]
  linarith [heightPartitionBump.nonneg (x := t/S)]

lemma smooth_height_integral_split (F : ℝ → ℂ) (hF : Integrable F) (S : ℝ) :
    (∫ t : ℝ, F t) =
      (∫ t : ℝ, (heightPartitionBump (t/S):ℂ)*F t)+
      ∫ t : ℝ, (1-(heightPartitionBump (t/S):ℂ))*F t := by
  have hb : Continuous (fun t : ℝ => (heightPartitionBump (t/S):ℂ)) :=
    Complex.continuous_ofReal.comp (heightPartitionBump.continuous.comp (continuous_id.div_const S))
  have h₁ : Integrable (fun t => (heightPartitionBump (t/S):ℂ)*F t) :=
    hF.bdd_mul hb.aestronglyMeasurable (Filter.Eventually.of_forall (height_bump_norm S))
  have h₂ : Integrable (fun t => (1-(heightPartitionBump (t/S):ℂ))*F t) :=
    hF.bdd_mul (continuous_const.sub hb).aestronglyMeasurable
      (Filter.Eventually.of_forall (height_bump_complement_norm S))
  rw [←integral_add h₁ h₂]
  apply integral_congr_ae
  filter_upwards with t
  ring

lemma smooth_mellin_central_bound (w F : ℝ → ℂ) (hw : Integrable w)
    {S B : ℝ} (hS : 0 < S) (hB : 0 ≤ B)
    (hF : ∀ t, |t| ≤ (4/3)*S → ‖F t‖ ≤ B) :
    ‖∫ t : ℝ, (heightPartitionBump (t/S):ℂ)*w t*F t‖ ≤
      (∫ t : ℝ, ‖w t‖)*B := by
  rw [←integral_mul_const]
  apply norm_integral_le_of_norm_le (hw.norm.mul_const B)
  filter_upwards with t
  by_cases ht : |t| ≤ (4/3)*S
  · rw [norm_mul,norm_mul]
    exact mul_le_mul
      ((mul_le_mul_of_nonneg_right (height_bump_norm S t) (_root_.norm_nonneg _)).trans_eq (one_mul _))
      (hF t ht) (_root_.norm_nonneg _) (_root_.norm_nonneg _)
  · have hz : heightPartitionBump (t/S) = 0 := by
      apply heightPartitionBump_zero
      rw [abs_div,abs_of_pos hS]
      apply (le_div_iff₀ hS).mpr
      exact (lt_of_not_ge ht).le
    simp only [hz,Complex.ofReal_zero,zero_mul,norm_zero]
    exact mul_nonneg (_root_.norm_nonneg _) hB

lemma smooth_mellin_model_tail_bound (w F : ℝ → ℂ) (q : ℕ)
    (hq : Integrable (fun t => |t|^q*‖w t‖))
    {S B : ℝ} (hS : 0 < S) (hB : 0 ≤ B) (hF : ∀ t, ‖F t‖ ≤ B) :
    ‖∫ t : ℝ, (1-(heightPartitionBump (t/S):ℂ))*w t*F t‖ ≤
      (B/S^q)*(∫ t : ℝ, |t|^q*‖w t‖) := by
  rw [←integral_const_mul]
  apply norm_integral_le_of_norm_le (hq.const_mul (B/S^q))
  filter_upwards with t
  by_cases ht : |t| ≤ S
  · have hz : heightPartitionBump (t/S) = 1 := by
      apply heightPartitionBump_one
      rw [abs_div,abs_of_pos hS]
      exact (div_le_one hS).mpr ht
    simp only [hz,Complex.ofReal_one,sub_self,zero_mul,norm_zero]
    positivity
  · have hts : S ≤ |t| := (lt_of_not_ge ht).le
    have hr : 1 ≤ |t|^q/S^q := (le_div_iff₀ (pow_pos hS q)).mpr
      (by simpa using pow_le_pow_left₀ hS.le hts q)
    rw [norm_mul,norm_mul]
    calc
      _ ≤ 1*‖w t‖*B := mul_le_mul
        (mul_le_mul_of_nonneg_right (height_bump_complement_norm S t) (_root_.norm_nonneg _))
        (hF t) (_root_.norm_nonneg _) (by positivity)
      _ ≤ (|t|^q/S^q)*‖w t‖*B := by gcongr
      _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductGaussMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the full signed Schwartz-height estimate to the actual
product Mellin weight, with independent norm phases on both coefficients. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem gauss_mellin_complement_log_saving
    (hpnt : PrimaryPrimePNT) {C Mα Mβ M : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ) (hM : 0 ≤ M)
    (j dα dβ a : ℕ) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hpos : tsupport V ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (P B : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X S u : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^2*(1+Real.log Z)^(3*a) → 0 < X →
      (1+Real.log Z)^Ct ≤ S →
      (∀ n ∈ P, primary n ∧ 1 ≤ norm n/A ∧ norm n/A ≤ 2) →
      (∀ n ∈ B, primary n ∧ Squarefree n ∧ Z/2 ≤ norm n ∧ norm n ≤ Z) →
      (∀ n ∈ B, ‖β n‖ ≤ M) →
      (∑ n ∈ P, ‖α n‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ n ∈ B, ‖β n‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ‖∫ τ : ℝ, (1-(heightPartitionBump (τ/S):ℂ))*zeroLineMellinWeight V X τ*
        ∑ c ∈ P, ∑ b ∈ B, α c*β b*gauss (c*b)*normTwist (u-τ) (c*b)‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(S*(1+Real.log Z)^j) := by
  obtain ⟨K,Ct,hK,hbound⟩ := schwartz_gauss_complement_log_saving hpnt hMV hC hHuxley
    hMα hMβ hM j dα dβ a (reflectedZeroMellinProfile V hV hpos hsm)
  refine ⟨K,Ct,hK,?_⟩
  intro P B α β Z A X S u hZ hA hAu hX hS hP hB hβ hαE hβE
  let αu := fun c => α c*normTwist u c
  let βu := fun b => β b*normTwist u b
  have hαu : (∑ c ∈ P, ‖αu c‖^2) ≤ Mα*A*(1+Real.log Z)^dα := by
    simpa only [αu,norm_twisted_coefficient] using hαE
  have hβu : (∑ b ∈ B, ‖βu b‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ := by
    simpa only [βu,norm_twisted_coefficient] using hβE
  have hu (b : Eisenstein) (hb : b ∈ B) : ‖βu b‖ ≤ M := by
    simpa only [βu,norm_twisted_coefficient] using hβ b hb
  have hh := hbound P B αu βu Z A X S hZ hA hAu hX hS hP hB hu hαu hβu
  have he : (∫ τ : ℝ, (1-(heightPartitionBump (τ/S):ℂ))*zeroLineMellinWeight V X τ*
      ∑ c ∈ P, ∑ b ∈ B, α c*β b*gauss (c*b)*normTwist (u-τ) (c*b)) =
      ∫ t : ℝ, (1-(heightPartitionBump (t/S):ℂ))*reflectedZeroMellinProfile V hV hpos hsm t*
        Complex.exp ((-Real.log X*t:ℝ)*Complex.I)*
        ∑ c ∈ P, ∑ b ∈ B, αu c*βu b*gauss (c*b)*normTwist t (c*b) := by
    rw [←integral_neg_eq_self]
    apply integral_congr_ae
    filter_upwards with t
    rw [neg_div,heightPartitionBump.neg,zeroLineMellinWeight_reflected_phase V hV hpos hsm hX,
      sub_neg_eq_add,gaussProduct_shift P B α β
        (fun c hc => (hP c hc).1) (fun b hb => (hB b hb).1)]
    dsimp only [αu,βu]
    ring
  rw [he]
  exact hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Norm transfer through the entire product Mellin line. The central
polynomial bound, derived Gauss complement and elementary model tail are
kept separate in this finite integral inequality. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma centered_mellin_integral_bound
    (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (hP : ∀ a ∈ P, primary a) (hB : ∀ b ∈ B, primary b)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) {X S Mc Mg Mm : ℝ}
    (hX : 0 < X) (hS : 0 < S) (hMc : 0 ≤ Mc) (hMm : 0 ≤ Mm) (u : ℝ)
    (hcentral : ∀ τ : ℝ, |τ| ≤ (4/3)*S →
      ‖centeredProductPolynomial P B α β 0 (u-τ)‖ ≤ Mc)
    (hmodel : ∀ t : ℝ, ‖squarefreeProductModel P B α β t‖ ≤ Mm)
    (hgauss : ‖∫ τ : ℝ, (1-(heightPartitionBump (τ/S):ℂ))*zeroLineMellinWeight V X τ*
      ∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*normTwist (u-τ) (a*b)‖ ≤ Mg) :
    ‖centeredProductSmoothed P B α β 0 V X u‖ ≤
      zeroLineMellinMass V*Mc+Mg+
        cStar*(Mm/S)*(∫ τ : ℝ, |τ| * ‖zeroLineMellinWeight V 1 τ‖) := by
  let w := zeroLineMellinWeight V X
  let c := fun τ => centeredProductPolynomial P B α β 0 (u-τ)
  let m := fun τ => squarefreeProductModel P B α β (u-τ)
  let g := fun τ => ∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*normTwist (u-τ) (a*b)
  let χ := fun τ => (1:ℂ)-(heightPartitionBump (τ/S):ℂ)
  have hw : Integrable w := zeroLineMellinWeight_integrable V hV hpos hsm hX
  have hc : Integrable (fun τ => w τ*c τ) :=
    centered_product_mellin_integrable P B α β 0 V hV hpos hsm hX u
  have hm : Integrable (fun τ => w τ*m τ) := by
    apply hw.mul_bdd (c := Mm)
    · have hcont : Continuous m := by
        convert (continuous_squarefreeProductModel P B α β 0).comp
          ((continuous_const : Continuous (fun _ : ℝ => u)).sub continuous_id) using 1
        all_goals try with_reducible_and_instances rfl
        funext τ
        simp only [m,Function.comp_def,Pi.sub_apply,id_eq,add_zero]
      exact hcont.aestronglyMeasurable
    · filter_upwards with τ
      exact hmodel (u-τ)
  have hχ : Continuous χ := continuous_const.sub
    (Complex.continuous_ofReal.comp (heightPartitionBump.continuous.comp (continuous_id.div_const S)))
  have hcχ : Integrable (fun τ => χ τ*(w τ*c τ)) :=
    hc.bdd_mul hχ.aestronglyMeasurable (Filter.Eventually.of_forall (height_bump_complement_norm S))
  have hmχ : Integrable (fun τ => χ τ*(w τ*m τ)) :=
    hm.bdd_mul hχ.aestronglyMeasurable (Filter.Eventually.of_forall (height_bump_complement_norm S))
  have hge : (fun τ => χ τ*w τ*g τ) =
      fun τ => χ τ*(w τ*c τ)+(cStar:ℂ)*(χ τ*(w τ*m τ)) := by
    funext τ
    have he := centered_product_eq_gauss_sub_model P B α β (u-τ)
    dsimp only [c,g,m]
    rw [he]
    ring
  have hgχ : Integrable (fun τ => χ τ*w τ*g τ) := by
    rw [hge]
    exact hcχ.add (hmχ.const_mul _)
  have htail : (∫ τ : ℝ, χ τ*(w τ*c τ)) =
      (∫ τ : ℝ, χ τ*w τ*g τ)-(cStar:ℂ)*(∫ τ : ℝ, χ τ*w τ*m τ) := by
    rw [hge,integral_add hcχ (hmχ.const_mul _),integral_const_mul]
    have hem : (fun τ => χ τ*w τ*m τ) = (fun τ => χ τ*(w τ*m τ)) := by
      funext τ; ring
    rw [hem]
    ring
  have hmodeltail := smooth_mellin_model_tail_bound w m 1
    (zeroLineMellinWeight_moment_integrable V hV hpos hsm hX 1) hS hMm
    (fun τ => hmodel (u-τ))
  have hmoment : (∫ τ : ℝ, |τ| * ‖w τ‖) =
      ∫ τ : ℝ, |τ| * ‖zeroLineMellinWeight V 1 τ‖ := by
    apply integral_congr_ae
    filter_upwards with τ
    rw [zeroLineMellinWeight_norm V hX,
      zeroLineMellinWeight_norm V (by norm_num : (0:ℝ) < 1)]
  simp only [pow_one] at hmodeltail
  rw [hmoment] at hmodeltail
  have hcenter := smooth_mellin_central_bound w c hw hS hMc hcentral
  rw [zeroLineMellinWeight_mass V hX] at hcenter
  simp_rw [mul_assoc] at hcenter
  have htailbound : ‖∫ τ : ℝ, χ τ*(w τ*c τ)‖ ≤
      Mg+cStar*(Mm/S)*(∫ τ : ℝ, |τ| * ‖zeroLineMellinWeight V 1 τ‖) := by
    rw [htail]
    apply (norm_sub_le _ _).trans
    apply add_le_add hgauss
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg cStar_pos.le]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmodeltail cStar_pos.le
  rw [centered_product_mellin P B α β hP hB 0 V hV hpos hsm hX u,
    smooth_height_integral_split _ hc S]
  exact (norm_add_le _ _).trans ((add_le_add hcenter htailbound).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit logarithmic choices for the full stopped product Mellin line. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_product_window_power {L t : ℝ} (hL : 2 ≤ L) (ht0 : 0 ≤ t) (ht : t ≤ L)
    (Ct s : ℕ) (hs : 2*Ct ≤ s) : (1+t)^Ct ≤ L^s := by
  calc
    _ ≤ (2*L)^Ct := pow_le_pow_left₀ (by linarith) (by linarith) Ct
    _ = 2^Ct*L^Ct := mul_pow _ _ _
    _ ≤ L^Ct*L^Ct := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num) hL Ct) (pow_nonneg (by linarith) _)
    _ = L^(2*Ct) := by rw [←pow_add]; congr 1; omega
    _ ≤ L^s := pow_le_pow_right₀ (by linarith) hs

lemma stopped_product_shift_power {L u τ : ℝ} (hL : 2 ≤ L)
    (H s : ℕ) (hu : |u| ≤ L^H) (hτ : |τ| ≤ (4/3)*L^s) :
    |u-τ| ≤ L^(H+s+2) := by
  have hL1 : 1 ≤ L := by linarith
  have hLH : L^H ≤ L^(H+s) := pow_le_pow_right₀ hL1 (by omega)
  have hLs : L^s ≤ L^(H+s) := pow_le_pow_right₀ hL1 (by omega)
  have hbase : 0 ≤ L^(H+s) := pow_nonneg (by linarith : 0 ≤ L) _
  calc
    _ ≤ |u|+|τ| := abs_sub _ _
    _ ≤ L^H+(4/3)*L^s := add_le_add hu hτ
    _ ≤ 3*L^(H+s) := by nlinarith
    _ = L^(H+s)*3 := by ring
    _ ≤ L^(H+s)*L^2 := mul_le_mul_of_nonneg_left
      (by nlinarith [sq_nonneg (L-2)] : (3:ℝ) ≤ L^2) hbase
    _ = _ := (pow_add _ _ _).symm

lemma stopped_product_model_scale {A b X : ℝ} (hA1 : 1 ≤ A) (hb : 1 ≤ b)
    (hX : Real.exp 1 ≤ X) (hbX : b ≤ X) (hAb : A ≤ b^2) (d : ℕ) :
    (2*(A*b))*(A*b/2)^(-1/6:ℝ)*(1+Real.log (2*(A*b)))^d ≤
      (4*5^d)*(A^(5/6:ℝ)*b^(5/6:ℝ))*(Real.log X)^d := by
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hbp : 0 < b := zero_lt_one.trans_le hb
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hL : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hlogb : Real.log b ≤ Real.log X := Real.log_le_log hbp hbX
  have hlogA : Real.log A ≤ 2*Real.log X := by
    have hh := Real.log_le_log hA hAb
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hlog : 1+Real.log (2*(A*b)) ≤ 5*Real.log X := by
    rw [Real.log_mul (by norm_num) (mul_pos hA hbp).ne',Real.log_mul hA.ne' hbp.ne']
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at htwo
    linarith
  have hscale : (2*(A*b))*(A*b/2)^(-1/6:ℝ) ≤
      4*(A^(5/6:ℝ)*b^(5/6:ℝ)) := by
    rw [Real.div_rpow (mul_pos hA hbp).le (by norm_num),div_eq_mul_inv,
      ←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    have hid : (A*b)*(A*b)^(-1/6:ℝ) = A^(5/6:ℝ)*b^(5/6:ℝ) := by
      nth_rw 1 [←Real.rpow_one (A*b)]
      rw [←Real.rpow_add (mul_pos hA hbp)]
      norm_num
      exact Real.mul_rpow hA.le hbp.le
    have ht : (2:ℝ)^(1/6:ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (1/6:ℝ) ≤ 1)
    have he : -(-1/6:ℝ) = 1/6 := by ring
    rw [he]
    calc
      _ = 2*((A*b)*(A*b)^(-1/6:ℝ))*(2:ℝ)^(1/6:ℝ) := by ring
      _ = 2*(A^(5/6:ℝ)*b^(5/6:ℝ))*(2:ℝ)^(1/6:ℝ) := by rw [hid]
      _ ≤ 2*(A^(5/6:ℝ)*b^(5/6:ℝ))*2 :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  have hlower : 0 ≤ 1+Real.log (2*(A*b)) := by
    have hab : 1 ≤ A*b := one_le_mul_of_one_le_of_one_le hA1 hb
    have hh := Real.log_nonneg (by linarith : 1 ≤ 2*(A*b))
    linarith
  calc
    _ ≤ (4*(A^(5/6:ℝ)*b^(5/6:ℝ)))*(5*Real.log X)^d :=
      mul_le_mul hscale (pow_le_pow_left₀ hlower hlog d)
        (pow_nonneg hlower _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

lemma stopped_product_power_absorb {L B K : ℝ} (hL : 1 ≤ L) (hB : 0 ≤ B)
    (hK : 0 ≤ K) (d k s : ℕ) (hs : d+k ≤ s) :
    K*B*L^d/L^s ≤ K*B/L^k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  apply (div_le_div_iff₀ (pow_pos hLp s) (pow_pos hLp k)).mpr
  calc
    _ = K*B*L^(d+k) := by rw [pow_add]; ring
    _ ≤ K*B*L^s := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hs) (mul_nonneg hK hB)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full product-weight transfer for the literal stopped outer coefficient.
The beta energy follows from its pointwise bound and primary support;
only the central polynomial estimate is left as a reusable argument. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem stopped_product_transfer (hpnt : PrimaryPrimePNT)
    {C M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hM : 0 ≤ M)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) :
    ∃ (Kg Km : ℝ) (d Ct : ℕ), 0 < Kg ∧ 0 < Km ∧
      ∀ (E U P B : Finset Eisenstein) (ψ : ℝ → ℝ) (w : ℝ)
        (remaining : Eisenstein → Prop) (β : Eisenstein → ℂ)
        (b A X S u Mc : ℝ),
      (65536:ℝ)^2 ≤ b → 2*b^(3/2:ℝ) ≤ A → A ≤ b^2 → 0 < X →
      (1+Real.log b)^Ct ≤ S → 0 ≤ Mc →
      (∀ e ∈ E, primary e) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      (∀ n ∈ P, primary n ∧ Squarefree n ∧ A ≤ norm n ∧ norm n ≤ 2*A) →
      (∀ n ∈ B, primary n ∧ Squarefree n ∧ b/2 ≤ norm n ∧ norm n ≤ b) →
      (∀ n ∈ B, ‖β n‖ ≤ M) →
      (∀ τ : ℝ, |τ| ≤ (4/3)*S →
        ‖centeredProductPolynomial P B (stoppedAlpha E U ψ w remaining) β 0 (u-τ)‖ ≤ Mc) →
      ‖centeredProductSmoothed P B (stoppedAlpha E U ψ w remaining) β 0 V X u‖ ≤
        zeroLineMellinMass V*Mc + Kg*A^(5/6:ℝ)*b^(5/6:ℝ)/S +
        cStar*(Km*M*(2*(A*b))*(A*b/2)^(-1/6:ℝ)*(1+Real.log (2*(A*b)))^d/S)*
          (∫ τ : ℝ, |τ| * ‖zeroLineMellinWeight V 1 τ‖) := by
  obtain ⟨Ka,da,hKa,halpha⟩ := stopped_outer_log_energy hpnt
  obtain ⟨Kg,Ct,hKg,hgauss⟩ := gauss_mellin_complement_log_saving hpnt hMV hC hHuxley
    hKa.le (show 0 ≤ 18*M^2 by positivity) hM 0 da 0 0 V hV hpos hsm
  obtain ⟨Km,d,hKm,hmodel⟩ := stopped_product_model_norm hpnt
  refine ⟨Kg,Km,d,Ct,hKg,hKm,?_⟩
  intro E U P B ψ w remaining β b A X S u Mc hb hA hAu hX hS hMc hE hψ hP hB hβ hc
  have hbp : 0 < b := by nlinarith
  have hb2 : 2 ≤ b := by nlinarith
  have hb1 : 1 ≤ b := by linarith
  have hAlo : b^(3/2:ℝ) ≤ A := by linarith [Real.rpow_nonneg hbp.le (3/2:ℝ)]
  have hAp : 0 < A := (Real.rpow_pos_of_pos hbp _).trans_le hAlo
  have hbpow : b ≤ b^(3/2:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hb1
      (by norm_num : (1:ℝ) ≤ 3/2)
  have hbA : b ≤ A := hbpow.trans hAlo
  have hbbig : Real.exp 1 ≤ b := by linarith [Real.exp_one_lt_d9]
  have hSpos : 0 < S := (pow_pos (by linarith [Real.log_nonneg hb1] : 0 < 1+Real.log b) Ct).trans_le hS
  have hαE : (∑ n ∈ P, ‖stoppedAlpha E U ψ w remaining n‖^2) ≤
      Ka*A*(1+Real.log b)^da := by
    exact (halpha E U P ψ w b A b remaining hE hψ hbbig hb2 le_rfl hAlo hAu hP).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.log_nonneg hb1) (by linarith) da) (by positivity))
  have hβE : (∑ n ∈ B, ‖β n‖^2) ≤ (18*M^2)*b*(1+Real.log b)^0 := by
    have hcard := primary_support_card_le B hbp.le (fun n hn => ⟨(hB n hn).1,(hB n hn).2.2.2⟩)
    calc
      _ ≤ ∑ _n ∈ B, M^2 := Finset.sum_le_sum (fun n hn =>
        pow_le_pow_left₀ (_root_.norm_nonneg _) (hβ n hn) 2)
      _ = (B.card:ℝ)*M^2 := by simp
      _ ≤ (18*b)*M^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg M)
      _ = _ := by ring
  have hg := hgauss P B (stoppedAlpha E U ψ w remaining) β b A X S u hb hA
    (by simpa using hAu) hX hS
    (fun n hn => ⟨(hP n hn).1,
      (le_div_iff₀ hAp).mpr (by simpa using (hP n hn).2.2.1),
      (div_le_iff₀ hAp).mpr (by simpa [mul_comm] using (hP n hn).2.2.2)⟩)
    hB hβ hαE hβE
  simp only [pow_zero,mul_one] at hg
  have hpair (a : Eisenstein) (ha : a ∈ P) (b' : Eisenstein) (hb' : b' ∈ B) :
      A*b/2 ≤ norm (a*b') ∧ norm (a*b') ≤ 2*(A*b) := by
    rw [norm_mul_eq]
    constructor
    · calc
        A*b/2 = A*(b/2) := by ring
        _ ≤ norm a*norm b' := mul_le_mul (hP a ha).2.2.1 (hB b' hb').2.2.1
          (by positivity) (norm_nonneg a)
    · calc
        _ ≤ (2*A)*b := mul_le_mul (hP a ha).2.2.2 (hB b' hb').2.2.2
          (norm_nonneg b') (by positivity)
        _ = _ := by ring
  have hY : Real.exp 1 ≤ 2*(A*b) := by
    have hbprod : b ≤ A*b := le_mul_of_one_le_left hbp.le (by linarith : 1 ≤ A)
    linarith
  have hlogY : 0 ≤ 1+Real.log (2*(A*b)) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hY
    rw [Real.log_exp] at hh
    linarith
  have hm := hmodel E U P B ψ w remaining β (A*b/2) (2*(A*b)) M
  exact centered_mellin_integral_bound P B (stoppedAlpha E U ψ w remaining) β
    (fun n hn => (hP n hn).1) (fun n hn => (hB n hn).1) V hV hpos hsm
    hX hSpos hMc
    (show 0 ≤ Km*M*(2*(A*b))*(A*b/2)^(-1/6:ℝ)*(1+Real.log (2*(A*b)))^d by positivity) u hc
    (fun t => hm t hE hψ hY (by positivity) hM
      (fun n hn => (hP n hn).1) (fun n hn => (hB n hn).1) hpair hβ) hg

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
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralStoppedProductLogSaving
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full Mellin cancellation for the literal stopped alpha and beta.
The central range uses the proved corrected dispersion; both signed
complements are bounded, so the original smooth product weight remains. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem stopped_product_bilinear_log_saving_actual
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
    {RΦ : ℝ} (hcut : ∀ x, RΦ < x → Φ x = 0)
    (Ω : ℝ → ℂ) (hΩ : HasCompactSupport Ω) (hΩpos : tsupport Ω ⊆ Set.Ioi 0)
    (hΩsm : ContDiff ℝ ∞ Ω) (k H : ℕ) :
    ∃ (d G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u v A X₀ : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X → 0 < X₀ →
      0 ≤ v → |u| ≤ (Real.log X)^H → 1+v ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ v) →
      2*b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(15*(2*k+d)) →
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
      ‖centeredProductSmoothed P S (stoppedAlpha E₀ U ψ w remaining) β 0 Ω X₀ u‖ ≤
        K*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k := by
  obtain ⟨M,hM,hcoeff⟩ := stopped_interval_energy (ι := ι) hξ hξz
  obtain ⟨Kg,Km,dm,Ct,hKg,hKm,htransfer⟩ := stopped_product_transfer hpnt hMV hC hHuxley
    hM.le Ω hΩ hΩpos hΩsm
  let s := 2*Ct+dm+k+1
  obtain ⟨d,G,Kc,hKc,hpoint⟩ := stopped_centered_bilinear_log_saving_actual (ι := ι) (E := E)
    hpnt hSW hMV hC hHuxley  hGamma hξ hξz hκ hF hJ
    Φ hΦnn hΦ hΦpos hΦ' hΦone hcut k (H+s+2)
  let I := ∫ τ : ℝ, |τ| * ‖zeroLineMellinWeight Ω 1 τ‖
  have hI : 0 ≤ I := integral_nonneg (fun τ => mul_nonneg (abs_nonneg _) (_root_.norm_nonneg _))
  let Km' := Km*M*(4*5^dm)
  have hKm' : 0 ≤ Km' := by dsimp [Km']; positivity
  have hmass : 0 ≤ zeroLineMellinMass Ω := zeroLineMellinMass_nonneg Ω
  have hcs : 0 < cStar := cStar_pos
  let K := zeroLineMellinMass Ω*Kc+Kg+cStar*Km'*I+1
  refine ⟨d,G,K,by dsimp [K]; positivity,?_⟩
  filter_upwards [hcoeff,hpoint,eventually_ge_atTop (Real.exp 2),
    (tendsto_rpow_atTop hκ).eventually_ge_atTop ((65536:ℝ)^2)]
    with X hcoeff hpoint hX hlarge
  intro δ b u v A X₀ hδ hδone hwidth hb hbXlo hbXhi hX₀ hv hu hvF W hW hWi hWd
    hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hR E₀ U P ψ w remaining hE₀ hψ hP
  dsimp only
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let L := Real.log X
  let B0 := A^(5/6:ℝ)*b^(5/6:ℝ)
  have hL2 : 2 ≤ L := by
    simpa only [L,Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hX
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hbp : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hAl : b^(3/2:ℝ) ≤ A := by linarith [Real.rpow_nonneg hbp.le (3/2:ℝ)]
  have hAp : 0 < A := (Real.rpow_pos_of_pos hbp _).trans_le hAl
  have hA1 : 1 ≤ A := (Real.one_le_rpow hb1 (by norm_num)).trans hAl
  have hAupper : A ≤ b^2 := hAhi.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hL1))
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hβ : ∀ r ∈ S, ‖β r‖ ≤ M := (hcoeff W hW _ 0 (b/2) b e hbp.le hbXhi).1
  have hS (r : Eisenstein) (hr : r ∈ S) :
      primary r ∧ Squarefree r ∧ b/2 ≤ norm r ∧ norm r ≤ b := by
    have hh := stoppedIntervalSupport_spec X (b/2) b e hr
    exact ⟨hh.1,hh.2.1,(Finset.mem_filter.mp hr).2.2.2.1.le,hh.2.2⟩
  have hwindow : (1+Real.log b)^Ct ≤ L^s :=
    stopped_product_window_power hL2 (Real.log_nonneg hb1)
      (Real.log_le_log hbp hbXhi) Ct s (by dsimp [s]; omega)
  have hc : ∀ τ : ℝ, |τ| ≤ (4/3)*L^s →
      ‖centeredProductPolynomial P S (stoppedAlpha E₀ U ψ w remaining) β 0 (u-τ)‖ ≤
        Kc*B0/L^k := by
    intro τ hτ
    have hshift := stopped_product_shift_power hL2 H s hu hτ
    have hh := hpoint δ b (u-τ) v A hδ hδone hwidth hb hbXlo hbXhi hv hshift hvF
      W hW hWi hWd hAl hAhi e he hNe j₀ k₀ h Z Q early hj hR E₀ U P ψ w remaining hE₀ hψ hP
    simpa only [centeredProductPolynomial,theta_zero,mul_one,B0,mul_assoc] using hh
  have ht := htransfer E₀ U P S ψ w remaining β b A X₀ (L^s) u (Kc*B0/L^k)
    (hlarge.trans hbXlo) hAlo hAupper hX₀ hwindow (by positivity) hE₀ hψ hP hS hβ hc
  have hgauss : Kg*B0/L^s ≤ Kg*B0/L^k := by
    simpa only [pow_zero,mul_one] using stopped_product_power_absorb hL1 hB0 hKg.le
      0 k s (by dsimp [s]; omega)
  have hX1 : Real.exp 1 ≤ X := (Real.exp_le_exp.mpr (by norm_num)).trans hX
  have hmodelscale := stopped_product_model_scale hA1 hb1 hX1 hbXhi hAupper dm
  have hmodel : Km*M*(2*(A*b))*(A*b/2)^(-1/6:ℝ)*(1+Real.log (2*(A*b)))^dm/L^s ≤
      Km'*B0/L^k := by
    apply (div_le_div_of_nonneg_right
      (show Km*M*(2*(A*b))*(A*b/2)^(-1/6:ℝ)*(1+Real.log (2*(A*b)))^dm ≤
          Km'*B0*L^dm by
        simpa only [Km',B0,L,mul_assoc] using
          mul_le_mul_of_nonneg_left hmodelscale (mul_nonneg hKm.le hM.le))
      (pow_nonneg hLp.le _)).trans
    exact stopped_product_power_absorb hL1 hB0 hKm' dm k s (by dsimp [s]; omega)
  have hgb : Kg*A^(5/6:ℝ)*b^(5/6:ℝ)/L^s = Kg*B0/L^s := by dsimp [B0]; ring
  rw [hgb] at ht
  apply ht.trans
  change zeroLineMellinMass Ω*(Kc*B0/L^k)+Kg*B0/L^s+
    cStar*(Km*M*(2*(A*b))*(A*b/2)^(-1/6:ℝ)*(1+Real.log (2*(A*b)))^dm/L^s)*I ≤ _
  calc
    _ ≤ zeroLineMellinMass Ω*(Kc*B0/L^k)+Kg*B0/L^k+cStar*(Km'*B0/L^k)*I :=
      add_le_add (add_le_add (le_refl _) hgauss)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmodel cStar_pos.le) hI)
    _ = (zeroLineMellinMass Ω*Kc+Kg+cStar*Km'*I)*B0/L^k := by ring
    _ ≤ K*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hLp.le _)
      calc
        _ ≤ K*B0 := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hB0
        _ = K*A^(5/6:ℝ)*b^(5/6:ℝ) := by dsimp [B0]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralStoppedProductLowSaving
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


theorem stopped_product_low_log_saving_actual
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
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      ‖∑ a ∈ P, ∑ b ∈ S, stoppedAlpha E₀ U ψ w remaining a*β b*
        centeredHeightKernel 0 Ω H ((1+Real.log X)^Ct) X₀ X₀ (a*b)‖ ≤
        K*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k := by
  obtain ⟨d,G,K,hK,hbound⟩ := stopped_product_bilinear_log_saving_actual (ι := ι)
    hpnt hSW hMV hC hHuxley  hGamma hξ hξz hκ hF hJ
    Φ hΦnn hΦ hΦpos hΦ' hΦone hcut Ω hΩ hΩpos hΩsm (k+Ct) (Ct+2)
  let K' := (8/3)*Real.log 2*(2:ℝ)^Ct*K
  refine ⟨d,G,K',by dsimp [K']; positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (Real.exp ((2:ℝ)^(Ct+2)))] with X hb hX
  intro δ b v A X₀ H hδ hδ1 hwidth hb2 hbκ hbX hX₀ hv hvF hH
    W hW hWs hWd hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hrough E₀ U P ψ w
    remaining hE₀ hψ hP
  dsimp only
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let α := stoppedAlpha E₀ U ψ w remaining
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
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralStoppedOrdinaryLowSaving
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


theorem ordinary_stopped_low_kernel_bound_actual_oai (i : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
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
        centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b)‖ ≤
        K*X^(5/6:ℝ)/(Real.log X)^k := by
  obtain ⟨V,hV,hweights⟩ := distinguishedStoppingWeights_uniform
  obtain ⟨d₀,G,K,hK,hbound⟩ := stopped_product_low_log_saving_actual (ι := Fin i)
    (κ := 1/4) (E := 0) (F := 1) (J := 1)
    hpnt hSW hMV hC hHuxley  hGamma hξ hξz (by norm_num) (by norm_num) (by norm_num)
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
  simp only [show 1+(ρ-1)=ρ by ring] at hh
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

theorem solution : type_of% @OAI.CubicFirstMoment.ordinary_stopped_low_kernel_bound_actual_oai := @OAI.CubicFirstMoment.ordinary_stopped_low_kernel_bound_actual_oai
