-- Prove2me | solution 1 for GeneratesNS.rho_g_case_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:04:27.624685+00:00
-- url     : https://prove2.me/submissions/ef1bb1d6-0364-41ab-98dd-e486a564cf12

import Mathlib
import Definitions.Def_OAIQ093D016

section
-- module Solutions.OAIQ093_PR.Defs
attribute [-instance] _root_.GeneratesNS.LipschitzH_normed _root_.GeneratesNS.LipschitzH_seminorm _root_.GeneratesNS.Lipschitz_finite_dimensional _root_.GeneratesNS.T2_W _root_.GeneratesNS.const_isClosed _root_.GeneratesNS.nonempty_basis _root_.GeneratesNS.proper_linear_w _root_.GeneratesNS.rho_g_FG _root_.GeneratesNS.volume_finite_compact _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The discrete Laplacian and the `G`-action

The Laplacian `Laplace_b` / `Laplace`, the constant functions `ConstF`, the quotient `W`, the
`G`-action `gAct`, and the closed-ball counting lemmas.

Root of the `Gromov.Defs` hierarchy: importing it pulls in the word metric, the measure
structure, `LipschitzH` and the convolution API.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Convolution
open MeasureTheory

lemma gAct_mul (g h : G) (f: LipschitzH ): gAct (g * h) f = gAct g (gAct h f) := by
  unfold gAct
  ext x
  simp [DFunLike.coe]
  rw [← mul_assoc]


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Vendor_Carleson_ToMathlib_MeasureTheory_Integral_MeanInequalities
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Vendored from the Carleson project

Port of `Carleson/ToMathlib/MeasureTheory/Integral/MeanInequalities.lean` from
<https://github.com/fpvandoorn/carleson> (branch `young-add-group`, commit `3b35c86`), which is
the non-abelian generalization of Young's convolution inequality.

The `eLpNorm_Ioc_convolution_le_*` theorems at the end of the upstream file are omitted: they are
unused here and would drag in the whole `Carleson/ToMathlib/MeasureTheory/Integral/Periodic.lean`
(`liftIoc`) development.
-/

set_option linter.style.header false

section

open NNReal ENNReal MeasureTheory Finset

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}


section Convolution

open scoped Convolution

namespace ENNReal

universe u𝕜 uG uE uE' uF

variable {𝕜 : Type u𝕜} {G : Type uG} [MeasurableSpace G] {μ : Measure G}
  {E : Type uE} {E' : Type uE'} {F : Type uF}

variable [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup F]
  {f : G → E} {g : G → E'}

/-- If `MemLp f p μ` and `MemLp g q μ`, where `p` and `q` are Hölder conjugates, then the
convolution of `f` and `g` exists everywhere.

This is `MeasureTheory.ConvolutionExists.of_memLp_memLp`, re-exported into the `ENNReal`
namespace to match the name used elsewhere in this development. -/
alias ConvolutionExists.of_memLp_memLp := MeasureTheory.ConvolutionExists.of_memLp_memLp

variable [NontriviallyNormedField 𝕜]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
variable {L : E →L[𝕜] E' →L[𝕜] F}

variable [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [BorelSpace G]
  [μ.IsAddHaarMeasure] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- Special case of **Young's convolution inequality** when `r = ∞`. -/
theorem eLpNorm_top_convolution_le [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace E'] [OpensMeasurableSpace E'] [μ.IsNegInvariant] {p q : ℝ≥0∞}
    (hpq : p.HolderConjugate q) {f : G → E} {g : G → E'} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) ∞ μ ≤ ENNReal.ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  refine eLpNorm_top_convolution_le_aux hpq hf.enorm ?_ ?_ c hL
  · intro x; exact (hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x)).enorm
  · intro x; exact eLpNorm_comp_measurePreserving' hg (μ.measurePreserving_sub_left x)

variable (L)

/-- **Young's convolution inequality**: the `L^r` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by `‖L‖ₑ` times the product of the `L^p` and `L^q` seminorms, where
`1 / p + 1 / q = 1 / r + 1`. Here `‖L‖ₑ` is replaced with a bound for `L` restricted to the ranges
of `f` and `g`; see `eLpNorm_convolution_le_enorm_mul` for a version using `‖L‖ₑ` explicitly. -/
theorem eLpNorm_convolution_le_of_norm_le_mul'
    [μ.IsAddRightInvariant] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ .ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  refine eLpNorm_convolution_le_of_norm_le_mul_aux hp hq hr hpqr hf.enorm ?_ ?_ ?_ c hL
  · intro x; exact hg.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x)
  · intro x; apply eLpNorm_comp_measurePreserving hg (μ.measurePreserving_sub_left x)
  · exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ) |>.enorm.pow_const _

/-- **Young's convolution inequality**: the `L^r` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by `‖L‖ₑ` times the product of the `L^p` and `L^q` seminorms, where
`1 / p + 1 / q = 1 / r + 1`. -/
theorem eLpNorm_convolution_le_enorm_mul' [μ.IsAddRightInvariant] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ ‖L‖ₑ * eLpNorm f p μ * eLpNorm g q μ := by
  rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg L)]
  exact eLpNorm_convolution_le_of_norm_le_mul' L hp hq hr hpqr hf hg ‖L‖ <| fun x y ↦
    ((L (f x)).le_opNorm (g y)).trans <| mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)

end ENNReal

end Convolution
end
end

section
-- module Solutions.OAIQ093_PR.Convolution
attribute [-instance] _root_.GeneratesNS.T2_W _root_.GeneratesNS.const_isClosed _root_.GeneratesNS.proper_linear_w _root_.GeneratesNS.rho_g_FG _root_.GeneratesNS.volume_finite_compact _root_.GeneratesNS.volume_mul_left_invariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Convolution on a finitely generated group
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

-- TODO - can we replace 'conv_assoc' with this?
lemma conv_assoc_of_lp2 {f g h: G → ℝ} (hf: MemLp f 2 Measure.count) (hg: MemLp g 2 Measure.count) (h_finsupp: h.support.Finite): Conv (Conv f g) h = Conv f (Conv g h) := by
  unfold Conv
  funext x


  have h_lp_n (n: ℕ): MemLp h n myHaarAddOpp := by
    apply Continuous.memLp_of_hasCompactSupport (X := Additive G) (μ := myHaarAddOpp)
    . apply continuous_of_discreteTopology
    .
      simp [HasCompactSupport]
      apply Set.Finite.isCompact
      simp [tsupport]
      exact h_finsupp

  conv =>
    lhs
    arg 1
    simp
    eta_reduce
  rw [MeasureTheory.convolution_assoc (L := ContinuousLinearMap.mul ℝ ℝ) (L₂ := ContinuousLinearMap.mul ℝ ℝ) (L₃ := ContinuousLinearMap.mul ℝ ℝ) (L₄ := ContinuousLinearMap.mul ℝ ℝ)]
  . rfl
  . intro x y z
    simp
    rw [mul_assoc]
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  .
    apply Filter.Eventually.of_forall
    intro a
    rw [my_add_haar_eq_count]
    apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
    . infer_instance
    . simp
    . apply AEStronglyMeasurable.of_discrete
    . apply AEStronglyMeasurable.of_discrete
    .
      exact hf
    . exact hg
  . apply Filter.Eventually.of_forall
    intro a
    rw [my_add_haar_eq_count]
    apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
    . infer_instance
    . simp
    . apply AEStronglyMeasurable.of_discrete
    . apply AEStronglyMeasurable.of_discrete
    .
      apply MeasureTheory.MemLp.abs
      exact hg
    . apply MeasureTheory.MemLp.abs
      rw [← my_add_haar_eq_count]
      apply h_lp_n
  .
    rw [my_add_haar_eq_count]
    apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
    . infer_instance
    . simp
    . apply AEStronglyMeasurable.of_discrete
    . apply AEStronglyMeasurable.of_discrete
    .
      apply MeasureTheory.MemLp.abs
      exact hf
    .
      unfold MeasureTheory.MemLp
      refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
      rw [← my_add_haar_eq_count]
      grw [ENNReal.eLpNorm_convolution_le_enorm_mul' (p := 2) (q := 1)]
      .
        simp
        apply ENNReal.mul_lt_top
        .
          simp_rw [← Real.norm_eq_abs]
          rw [MeasureTheory.eLpNorm_norm]
          rw [my_add_haar_eq_count]
          exact MemLp.eLpNorm_lt_top hg
        .
          simp_rw [← Real.norm_eq_abs]
          rw [MeasureTheory.eLpNorm_norm]
          rw [my_add_haar_eq_count]
          rw [← my_add_haar_eq_count]
          have foo := h_lp_n 1
          simp at foo
          exact MemLp.eLpNorm_lt_top foo
      . simp
      . simp
      . simp
      . simp
      . apply AEStronglyMeasurable.of_discrete
      . apply AEStronglyMeasurable.of_discrete

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Harmonic_Convolution
attribute [-instance] _root_.GeneratesNS.T2_W _root_.GeneratesNS.const_isClosed _root_.GeneratesNS.proper_linear_w _root_.GeneratesNS.rho_g_FG _root_.GeneratesNS.volume_finite_compact _root_.GeneratesNS.volume_mul_left_invariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Convolution and the Laplacian

Basic compatibility of the discrete Laplacian with convolution: additivity, scalar
multiplication, and `laplace_conv_eq_laplace_right`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS


variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]


open scoped Finset
open scoped Pointwise


open scoped Convolution
open MeasureTheory


lemma laplace_b_const (k: ℝ): Laplace_b (fun g => k) = 0 := by
  simp [Laplace_b]
  simp [f_conv_mu]
  ext a
  simp
  norm_cast
  rw [← mul_assoc]

  rw [inv_mul_cancel₀]
  . simp
  . simp
    have foo := S_nonempty
    grind


lemma laplace_conv_eq_laplace_right_of_lp2 (f g: G → ℝ) (hfg: ConvExists f g) (hf: MemLp f 2 Measure.count) (hg: MemLp g 2 Measure.count): Laplace_b (Conv f g) = Conv f (Laplace_b g) := by
  simp_rw [Laplace_b]
  rw [conv_assoc_of_lp2]

  nth_rw 2 [sub_eq_add_neg]
  rw [conv_add_right]
  -- TODO - figure out how to do this without a 'conv' block
  conv =>
    rhs
    rhs
    equals Conv f ((-1 : ℝ) • (Conv g (mu ))) =>
      simp
  rw [smul_conv]
  simp
  . rw [← sub_eq_add_neg]
  . exact hfg
  .
    simp [ConvExists, MeasureTheory.ConvolutionExists, MeasureTheory.ConvolutionExistsAt]
    intro a
    simp_rw [f_conv_mu]
    simp_rw [← mul_assoc, mul_comm, mul_assoc]
    apply MeasureTheory.Integrable.const_mul
    simp_rw [Finset.mul_sum]
    apply MeasureTheory.integrable_finset_sum
    intro s hs
    simp [ConvExists, MeasureTheory.ConvolutionExists, MeasureTheory.ConvolutionExistsAt] at hfg
    specialize hfg (s * a)
    simp_rw [mul_div]
    exact hfg
  . exact hf
  . exact hg
  . apply mu_finsupp


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Harmonic_MuConv
attribute [-instance] _root_.GeneratesNS.T2_W _root_.GeneratesNS.const_isClosed _root_.GeneratesNS.proper_linear_w _root_.GeneratesNS.rho_g_FG _root_.GeneratesNS.volume_finite_compact _root_.GeneratesNS.volume_mul_left_invariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Iterated convolution with `mu`

`mu_conv_eq_sum` expressing `muConv` as a sum over tuples, its nonnegativity and `L¹` norm, and
the telescoping identity `f_n_sub_conv`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

lemma integral_eq_eq_sum (f: G → ℝ) (hf: Integrable f): (∫ (g: G), f g) = (∑' (g : G), f g) := by
  rw [MeasureTheory.integral_countable]
  .
    simp [MeasureTheory.volume]
    simp_rw [my_haar_eq_count]
    simp
  . apply hf


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Harmonic_LaplaceLinear
attribute [-instance] _root_.GeneratesNS.T2_W _root_.GeneratesNS.const_isClosed _root_.GeneratesNS.proper_linear_w _root_.GeneratesNS.rho_g_FG _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Laplacian as a linear map on `L²`

`Laplace_linear`, the normalised functions `F_n`, and the limit `F_n_conv_mu_lim`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

lemma counting_le_essSup (f: G → ℝ): ∀ g : G, ‖f g‖ₑ ≤ essSup  (fun g => ‖f g‖ₑ) volume := by
  intro g
  have ae_le := ENNReal.ae_le_essSup (fun g => ‖f g‖ₑ) (μ := volume)
  simp [MeasureTheory.volume] at ae_le
  rw [my_haar_eq_count] at ae_le
  rw [count_ae_everywhere] at ae_le
  specialize ae_le g
  simp
  simp [volume]
  rw [my_haar_eq_count]
  exact ae_le

lemma essSup_eq_elpNorm_top (f: G → ℝ): (essSup (fun g => ‖f g‖ₑ) volume) = (eLpNorm f ⊤ volume) := by
  rfl


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Harmonic_Proposition318
attribute [-instance] _root_.GeneratesNS.T2_W _root_.GeneratesNS.const_isClosed _root_.GeneratesNS.proper_linear_w _root_.GeneratesNS.rho_g_FG _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Proposition 3.18

`proposition_3_18` and the auxiliary functions `G_n` used to produce an almost-harmonic
sequence.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

open scoped RealInnerProductSpace


lemma measure_preserving_inv: MeasurePreserving Inv.inv ((MeasureTheory.volume (α := G))) (MeasureTheory.volume (α := G)) := {
  measurable := by
    exact measurable_inv
  map_eq := by
    simp [volume]
    simp [my_haar_eq_count]
}


lemma measure_preserving_unop_tomul: MeasurePreserving (fun (x: Additive (G)) ↦ (Additive.toMul x)) myHaarAddOpp volume := by
  apply MeasureTheory.MeasurePreserving.id


lemma lp_summable {p: ℕ} (hp: 0 < p) (f: (Lp ℝ p volume (α := G))): Summable (fun g: G => |(f g)|^p) := by
  have f_norm := (MeasureTheory.Lp.memLp f).2
  simp [eLpNorm, eLpNorm'] at f_norm
  have not_le: ¬(p = 0) := by linarith
  simp [not_le] at f_norm
  rw [lintegral_g_eq_add] at f_norm
  rw [lt_top_iff_ne_top] at f_norm
  rw [Ne] at f_norm
  rw [ENNReal.rpow_eq_top_iff] at f_norm
  simp at f_norm
  simp [not_le] at f_norm
  simp_rw [Real.enorm_eq_ofReal_abs] at f_norm
  conv at f_norm =>
    arg 1
    lhs
    arg 1
    intro g
    rw [← ENNReal.ofReal_pow (by simp)]
  apply ENNReal.summable_toReal at f_norm
  conv at f_norm =>
    arg 1
    intro x
    rw [ENNReal.toReal_ofReal (by
      simp
    )]
  exact f_norm

lemma lp2_summable (f: (Lp ℝ 2 volume (α := G))): Summable (fun g: G => (f g)^2) := by
  conv =>
    arg 1
    intro g
    rw [← sq_abs]
  apply lp_summable (p := 2) (by simp) f


lemma summable_f_mul_translate (f: (Lp ℝ 2 volume (α := G))) (i: G): Summable (fun x => (f x) * (f (i * x))) := by
  have lp_mul := (MeasureTheory.MemLp.mul (φ := f) (f := fun x => f (i * x)) (p := 2) (q := 2) (r := 1) (μ := volume) ?_ ?_).2
  .
    simp [MemLp, eLpNorm, eLpNorm'] at lp_mul
    rw [lintegral_g_eq_add] at lp_mul
    simp [Real.enorm_eq_ofReal_abs] at lp_mul
    simp [← ENNReal.ofReal_mul] at lp_mul
    rw [lt_top_iff_ne_top] at lp_mul
    apply ENNReal.summable_toReal at lp_mul
    conv at lp_mul =>
      arg 1
      intro x
      rw [ENNReal.toReal_ofReal (by
        apply mul_nonneg
        . simp
        . simp
      )]
    apply Summable.of_abs
    simp_rw [abs_mul]
    exact lp_mul
  .
    rw [← Function.comp_def]
    apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
    . apply MeasureTheory.Lp.memLp f
    . exact measurePreserving_mul_left volume i
  . apply Lp.memLp f


-- Note - this is stated incorrectly in Vikman
-- The RHS should have a squared norm
set_option maxRecDepth 40000 in
lemma proposition_3_18 (f: (Lp ℝ 2 volume (α := G))): (∑' g: G, (f g) * (Laplace f) g) = ((2) * (#(S) : ℝ))⁻¹ * ∑ s ∈ S, ‖(f - (conv_finsupp_lp2 f (delta s) (by simp [delta])))‖^2 := by
  simp_rw [Laplace]
  simp_rw [conv_mu_lp2]
  simp_rw [f_conv_mu]
  conv =>
    enter [1, 1, g, 2, 1, 1, 2, 1, g, 2, 2, s]
    rw[ ← inv_inv s]
    rw [← f_conv_delta (s := s⁻¹) (f := f.val.cast)]

  simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
  simp only [Pi.sub_apply]
  conv =>
    lhs
    arg 1
    intro g
    lhs
    rw [← inv_mul_cancel_left₀ (a := 2) (by simp) (f g)]


  simp_rw [mul_assoc]
  rw [Summable.tsum_mul_left]
  simp_rw [← mul_assoc]

  conv =>
    lhs
    rhs
    arg 1
    intro g
    rw [mul_sub]
  rw [Summable.tsum_sub]
  have sum_f: ∀ c: ℝ, c = (#(S) : ℝ)⁻¹ * ∑ s ∈ S, c := by
    intro g
    simp
    have card_nonneg: #(S) ≠ 0 := by
      exact Finset.card_ne_zero.mpr S_nonempty
    field_simp
  conv =>
    lhs
    rhs
    lhs
    arg 1
    intro g
    rw [mul_assoc]
    rw [← pow_two]
    rw [sum_f (c := (f g)^2)]

  rw [Summable.tsum_mul_left]
  rw [Summable.tsum_mul_left]
  have f_norm := MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (p := 2) (by simp) (by simp) (f := f.val.cast) (μ := volume (α := G))
  simp_rw [lintegral_g_eq_add] at f_norm
  simp [enorm] at f_norm
  apply_fun ENNReal.toReal at f_norm
  norm_cast at f_norm
  rw [← ENNReal.toReal_rpow] at f_norm
  rw [ENNReal.tsum_toReal_eq] at f_norm
  simp at f_norm
  apply_fun (fun x => x^2) at f_norm
  nth_rw 2 [← Real.rpow_natCast] at f_norm
  rw [← Real.rpow_mul] at f_norm
  simp at f_norm
  have f_summable := lp_summable (p := 2) (by simp) f
  conv =>
    lhs
    rhs
    lhs
    rhs
    rhs
    rw [Summable.tsum_finsetSum (by
      intro i hi
      apply lp2_summable
    )]
    rw [← f_norm]

  conv =>
    lhs
    rhs
    rhs
    arg 1
    intro b
    rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    rw [← mul_assoc]
    rw [mul_comm (2 * _)]
    rw [mul_assoc]
    rw [mul_assoc]
    rw [Finset.mul_sum]
    rw [← mul_assoc]

  rw [Summable.tsum_mul_left]
  rw [Summable.tsum_finsetSum (by
    intro i hi
    simp [f_conv_delta]
    apply summable_f_mul_translate
  )]
  simp_rw [f_conv_delta]
  simp only [inv_inv]
  let f_conv := fun (s: G) => conv_finsupp_lp2 f (delta s) (by
    simp [delta]
  )
  have real_inner : ∀ a b : ℝ, ⟪a, b⟫ = a * b := fun a b => by rw [show (⟪a, b⟫ : ℝ) = b * a from rfl, mul_comm]
  have inner_f_conv := fun (s: G) => MeasureTheory.L2.inner_def (𝕜 := ℝ) (f := f) (g := f_conv s)
  simp [f_conv, conv_finsupp_lp2] at inner_f_conv
  simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at inner_f_conv
  conv at inner_f_conv =>
    intro a
    rhs
    -- TODO  - deduplicate this with the 'have lp_mul' block above
    rw [MeasureTheory.integral_countable (by
      simp [f_conv_delta]
      simp [Integrable]
      refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
      simp [HasFiniteIntegral]
      simp [Real.enorm_eq_ofReal_abs]
      rw [lintegral_g_eq_add]
      rw [lt_top_iff_ne_top]
      simp_rw [← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul]
      rw [← ENNReal.ofReal_tsum_of_nonneg]
      . apply ENNReal.ofReal_ne_top
      . intro n
        positivity
      .
        apply Summable.abs
        simp_rw [mul_comm]
        apply summable_f_mul_translate
    )]
  simp [volume, my_haar_eq_count, f_conv_delta] at inner_f_conv
  conv =>
    lhs
    rhs
    rhs
    rhs
    arg 1
    rw [S_eq_Sinv ]

  simp only [Finset.sum_inv_index]

  simp_rw [mul_comm] at inner_f_conv
  simp_rw [← inner_f_conv]
  -- Split '2 * ‖f‖^2 into two copies of ‖f‖^2, and convert one into ‖Conv f delta‖^2
  rw [two_mul]
  conv =>
    lhs
    rhs
    lhs
    lhs
    rhs
    arg 2
    intro s
    rw [← MeasureTheory.eLpNorm_comp_measurePreserving (f := fun x => s⁻¹ * x) (ν := volume) (by apply AEStronglyMeasurable.of_discrete) (by apply measurePreserving_mul_left)]


  simp_rw [Function.comp_def]
  simp_rw [← f_conv_delta]
  have card_s_ne: #(S) ≠ 0 := by
    simp
    exact Finset.nonempty_iff_ne_empty.mp S_nonempty
  simp_rw [norm_sub_sq_real]
  simp only [MeasureTheory.Lp.norm_def]
  simp_rw [conv_finsupp_lp2]
  simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  eta_reduce
  ring
  . apply summable_sum
    intro s hs
    simp_rw [f_conv_delta]
    apply summable_f_mul_translate
  .
    apply tsum_nonneg
    intro g
    apply sq_nonneg
  . simp
  . apply summable_sum
    intro s hs
    apply lp2_summable
  .
    apply Summable.mul_left
    apply summable_sum
    intro s hs
    apply lp2_summable
  . simp_rw [mul_assoc]
    apply Summable.mul_left
    simp_rw [← pow_two]
    apply lp2_summable
  . simp_rw [mul_assoc]
    apply Summable.mul_left
    rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    simp_rw [← mul_assoc]
    simp_rw [Finset.mul_sum]
    apply summable_sum
    intro s hs
    simp_rw [f_conv_delta]
    simp_rw [mul_comm]
    simp_rw [mul_assoc]
    apply Summable.mul_left
    apply summable_f_mul_translate
  .
    apply Summable.mul_left
    rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    simp_rw [mul_sub]
    apply Summable.sub
    . simp_rw [← pow_two]
      apply lp2_summable
    .
      simp_rw [← mul_assoc]
      simp_rw [Finset.mul_sum]
      apply summable_sum
      intro s hs
      simp_rw [f_conv_delta]
      simp_rw [mul_comm]
      simp_rw [mul_assoc]
      apply Summable.mul_left
      apply summable_f_mul_translate

lemma g_n_laplace_enorm_le (n: ℕ) (hn: 0 < n) (hf: f_n_conv_delta_tendsto): ‖Laplace (G_n n hn hf)‖ₑ ≤ 1/n := by
  have g_n_prop := (laplace_g_n n hn hf).choose_spec
  rw [← ofReal_norm]
  rw [show ((1 : ENNReal)/(n : ENNReal)) = ENNReal.ofReal (1/(n:ℝ)) by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_one,
      ENNReal.ofReal_natCast]]
  exact ENNReal.ofReal_le_ofReal g_n_prop.1


open scoped RealInnerProductSpace in
lemma g_n_conv_norm (n: ℕ) (hn: 0 < n) (hf: f_n_conv_delta_tendsto): ⟪Laplace (G_n n hn hf), (G_n n hn hf)⟫ = 1 := by
  have g_n_prop := (laplace_g_n n hn hf).choose_spec
  exact g_n_prop.2


lemma g_sub_norm_gt (hf: f_n_conv_delta_tendsto) (n: ℕ) : ∃ s ∈ S, ‖(G_n (n + 1) (by simp) hf) - (conv_finsupp_lp2 (G_n (n + 1) (by simp) hf) (delta s) (by simp [delta]))‖^2 > 1 := by
  by_contra!
  have card_le := Finset.sum_le_card_nsmul S _ (1 : ℝ) this
  have sum_norm := (proposition_3_18 (G_n (n + 1) (by simp) hf) )
  have g_inner_laplace := MeasureTheory.L2.inner_def (Laplace (G_n (n + 1) (by simp) hf)) (G_n (n + 1) (by simp) hf) (𝕜 := ℝ) (α := G)
  have g_n_prop := (Classical.choose_spec (laplace_g_n (n + 1) (by simp) hf)).2
  have real_inner : ∀ a b : ℝ, ⟪a, b⟫ = b * a := fun a b => rfl
  rw [integral_eq_eq_sum] at g_inner_laplace
  .
    simp_rw [real_inner] at g_inner_laplace
    simp_rw [← g_inner_laplace] at sum_norm
    nth_rw 1 [G_n] at sum_norm
    nth_rw 1 [G_n] at sum_norm
    rw [g_n_prop] at sum_norm
    rw [eq_inv_mul_iff_mul_eq₀] at sum_norm
    simp at sum_norm
    rw [← sum_norm] at card_le
    simp at card_le
    rw [mul_le_iff_le_one_left] at card_le
    . norm_num at card_le
    . simp
      have foo := S_nonempty
      grind
    .
      simp
      grind

  .
    rw [MeasureTheory.L2.inner_def] at g_n_prop
    apply MeasureTheory.integrable_of_integral_eq_one at g_n_prop
    exact g_n_prop


lemma g_sub_norm_single_s (hf: f_n_conv_delta_tendsto): ∃ s ∈ S, { n: ℕ | ‖(G_n (n + 1) (by simp) hf) - (conv_finsupp_lp2 (G_n (n + 1) (by simp) hf) (delta s) (by simp [delta]))‖^2 > 1 }.Infinite := by

  have frequent := Filter.Frequently.of_forall (f := Filter.atTop) (g_sub_norm_gt hf)
  simp at frequent
  obtain ⟨s, s_mem, s_frequently⟩ := frequent
  rw [Nat.frequently_atTop_iff_infinite] at s_frequently
  use s
  refine ⟨s_mem, ?_⟩
  simpa using s_frequently


lemma lipschitzWith_mul_prod  {K: Type*} [RCLike K] (f: G → K) {C: NNReal} (hf: ∀ g: G, ∀ s ∈ S, dist (f (s*g)) (f (g)) ≤ C)
  (g: G) (s: List S): dist (f (s.unattach.prod * g)) (f g) ≤ C * s.length := by

  induction s with
  | nil =>
    simp
  | cons head tail ih =>
    simp
    have triangle := dist_triangle (f (head * tail.unattach.prod * g)) (f (tail.unattach.prod * g)) (f g)
    grw [triangle]
    grw [ih]
    rw [mul_assoc]
    grw [hf _ _ (by simp)]
    grind


lemma lipschitzWith_discrete {K: Type*} [RCLike K] (f: G → K) {C: NNReal} (hf: ∀ g: G, ∀ s ∈ S, dist (f (s*g)) (f (g)) ≤ C):
    LipschitzWith C f := by

  apply LipschitzWith.of_dist_le_mul
  intro x y

  have prod_eq := word_norm_prod (y * x⁻¹) (WordNorm (y * x⁻¹)) rfl
  obtain ⟨l, l_prod, l_len⟩ := prod_eq
  simp [ProdS] at l_prod

  have mul_prod := lipschitzWith_mul_prod f hf x l
  simp [l_prod] at mul_prod
  rw [dist_comm]
  grw [mul_prod]
  simp [dist, WordDist, l_len]


lemma conv_neg_left (f g: G → ℝ): Conv (-f) g = -(Conv f g) := by
  conv =>
    pattern -f
    equals (-1 : ℝ) • f => simp

  rw [conv_smul]
  simp

lemma laplace_b_sub (f g: G → ℝ): Laplace_b (f - g) = Laplace_b f - Laplace_b g := by
  simp [Laplace_b]
  nth_rw 3 [sub_eq_add_neg]
  rw [conv_add_left]
  .
    rw [conv_neg_left]
    ring_nf
  .
    apply conv_exists_fin_supp
    right
    apply mu_finsupp
  . apply conv_exists_fin_supp
    right
    apply mu_finsupp


-- DO NOT REMOVE `f_n_limit` - this will be needed by the spectral theorem part of the proof

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Harmonic_CaseOne
attribute [-instance] _root_.GeneratesNS.T2_W _root_.GeneratesNS.const_isClosed _root_.GeneratesNS.proper_linear_w _root_.GeneratesNS.rho_g_FG _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Existence of a nontrivial harmonic function: first case

`nontrivial_harmonic_case_one`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

open scoped RealInnerProductSpace

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma nontrivial_harmonic_case_one (f_n_limit: ∀ s: S, (Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0))): ∃ F: LipschitzH , ∀ z: ℝ, F ≠ ConstLipschitzH z := by


  let H_n (n: ℕ) (s: G): (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) :=
    (1 / (‖(((G_n (n + 1) (by simp) f_n_limit) - (conv_finsupp_lp2 (G_n (n + 1) (by simp) f_n_limit) (delta s) (by simp [delta]))))‖)) •
      MeasureTheory.Lp.compMeasurePreserving (Inv.inv) (measure_preserving_inv) (((G_n (n + 1) (by simp) f_n_limit) - (conv_finsupp_lp2 (G_n (n + 1) (by simp) f_n_limit) (delta s) (by simp [delta]))))

  obtain ⟨s, s_mem_S, s_infinite⟩ := g_sub_norm_single_s f_n_limit
  let seq := Nat.nth ({n | ‖(G_n (n + 1) (by simp) f_n_limit) - (conv_finsupp_lp2 (G_n (n + 1) (by simp) f_n_limit) (delta s) (by simp))‖ ^ 2 > 1})
  have seq_mono : StrictMono seq := Nat.nth_strictMono s_infinite


  have H_n_norm (n: ℕ): ‖H_n (seq n) s‖ₑ = 1 := by
    conv =>
      rhs
      equals ‖(1: ℝ)‖ₑ => simp
    rw [enorm_eq_iff_norm_eq]
    unfold H_n
    have norm_gt := Nat.nth_mem_of_infinite s_infinite n
    rw [norm_smul]
    rw [MeasureTheory.Lp.norm_compMeasurePreserving]
    field_simp
    simp
    rw [mul_inv_cancel₀]
    simp [seq]
    simp at norm_gt
    by_contra!
    simp only [Set.ofPred] at this
    simp [this] at norm_gt
    norm_num at norm_gt

  have seq_add_pos: ∀ {n}, 0 < (seq (n + 1)) := by
    intro n
    have prev_lt := (seq_mono.lt_iff_lt (a := n) (b := n + 1)).mpr (by simp)
    grind

  have h_n_f_lipschitz: ∀ n: ℕ, LipschitzWith ((2 * #(S))^((2 : ℝ)⁻¹)) (Conv (H_n (seq (n)) s) (G_n ((seq n) + 1) (by simp) f_n_limit)) := by
    intro n
    let G'_n := (G_n ((seq n) + 1) (by simp))
    apply lipschitzWith_discrete
    intro g y hy
    rw [Real.dist_eq]
    rw [← Real.norm_eq_abs]
    rw [norm_sub_rev]
    have y_eq_inv_inv: y = y⁻¹⁻¹ := by simp
    rw [y_eq_inv_inv]
    rw [← f_conv_delta (f := Conv (↑↑(H_n (seq (n)) s)) (G_n ((seq n) + 1) (by simp) f_n_limit))]
    rw [← Pi.sub_apply]
    rw [sub_eq_add_neg]
    rw [← neg_one_smul ℝ]
    rw [← conv_smul]
    rw [ ← smul_conv]
    rw [conv_assoc_of_lp2]
    .
      rw [← conv_add_right]
      .
        rw [← ENNReal.ofReal_le_ofReal_iff]
        .
          rw [ofReal_norm_eq_enorm]
          grw [counting_le_essSup]
          rw [essSup_eq_elpNorm_top]
          simp only [volume]
          simp_rw [my_haar_eq_count]
          rw [← my_haar_eq_count]
          conv =>
            lhs
            arg 1
            arg 0
            unfold Conv
          eta_reduce
          simp_rw [my_haar_eq_count]
          conv =>
            arg 1
            arg 3
            equals myHaarAddOpp =>
              exact my_add_haar_eq_count.symm

          refine le_trans (ENNReal.eLpNorm_top_convolution_le (μ := myHaarAddOpp) (c := 1) (p := 2) (q := 2) (hpq := inferInstance) (by apply AEMeasurable.of_discrete) (by apply AEMeasurable.of_discrete) (by intro a b; simp)) ?_
          .
            simp [norm, volume] at H_n_norm
            rw [my_add_haar_eq_count]
            simp [H_n_norm]

            have sum_norm := proposition_3_18 (G'_n f_n_limit)
            have g_inner_laplace := MeasureTheory.L2.inner_def (Laplace (G'_n f_n_limit)) (G'_n f_n_limit) (𝕜 := ℝ) (α := G)
            have g_n_prop := (Classical.choose_spec (laplace_g_n (n + 1) (by simp) f_n_limit)).2
            rw [integral_eq_eq_sum] at g_inner_laplace
            replace g_inner_laplace := g_inner_laplace.trans sum_norm
            rw [g_n_conv_norm _ _ f_n_limit] at g_inner_laplace
            rw [inv_mul_eq_div] at g_inner_laplace
            rw [eq_div_iff_mul_eq] at g_inner_laplace

            .
              simp [eLpNorm, eLpNorm']
              simp [-AddSubgroupClass.coe_sub, -AddSubgroup.coe_sub, MeasureTheory.Lp.norm_def, eLpNorm, eLpNorm', conv_finsupp_lp2] at g_inner_laplace
              rw [← ENNReal.ofReal_rpow_of_pos]
              .
                have hkey : (∫⁻ (a : Additive G), ‖(H_n (seq n) s : Additive G → ℝ) a‖ₑ ^ 2 ∂Measure.count) ^ (2 : ℝ)⁻¹ = 1 := by
                  have h := H_n_norm n
                  show (∫⁻ (a : G), ‖(H_n (seq n) s : G → ℝ) a‖ₑ ^ 2 ∂Measure.count) ^ (2 : ℝ)⁻¹ = 1
                  simpa [MeasureTheory.Lp.enorm_def, eLpNorm, eLpNorm', one_div, volume,
                    my_haar_eq_count] using h
                rw [hkey, one_mul]
                apply ENNReal.rpow_le_rpow
                .
                  generalize_proofs p_1 p_2 p_3
                  -- TODO - make this less horrible
                  grw [Finset.single_le_sum (f := (fun g => ∫⁻ (a : Additive G), ‖(G_n ((seq n) + 1) (by simp) f_n_limit) a + Conv (-↑↑(G_n ((seq n) + 1) (by simp) f_n_limit)) (delta g) a‖ₑ ^ 2 ∂Measure.count)) (s := S) (hf := by simp) (h := (by rw [S_eq_Sinv]; simp [hy]))]


                  simp_rw [← ENNReal.rpow_natCast] at g_inner_laplace
                  simp_rw [← ENNReal.toReal_pow] at g_inner_laplace
                  simp_rw [← ENNReal.rpow_natCast] at g_inner_laplace
                  simp_rw [← ENNReal.rpow_mul] at g_inner_laplace
                  simp  [-AddSubgroupClass.coe_sub, -AddSubgroup.coe_sub] at g_inner_laplace
                  simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)] at g_inner_laplace
                  simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at g_inner_laplace
                  simp at g_inner_laplace
                  rw [← neg_one_smul ℝ]
                  simp_rw [conv_smul]
                  simp
                  simp_rw [← sub_eq_add_neg]
                  simp [G'_n] at g_inner_laplace
                  apply_fun ENNReal.ofReal at g_inner_laplace
                  simp at g_inner_laplace
                  rw [g_inner_laplace]
                  norm_cast
                  rw [ENNReal.ofReal_sum_of_nonneg]
                  .
                    conv =>
                      rhs
                      arg 2
                      intro i
                      rw [ENNReal.ofReal_toReal (by
                        simp [f_conv_delta_helper]
                        have g_norm := MeasureTheory.Lp.eLpNorm_lt_top ((G_n ((seq n) + 1) (by simp) f_n_limit) - (Lp.compMeasurePreserving (fun x => i⁻¹ * x) (by
                          apply measurePreserving_mul_left
                        ) (G_n ((seq n) + 1) (by simp) f_n_limit)))
                        rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at g_norm
                        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)] at g_norm
                        simp [eLpNorm, eLpNorm', Lp.compMeasurePreserving] at g_norm
                        rw [ENNReal.rpow_lt_top_iff_of_pos (by simp)] at g_norm
                        grind
                      )]
                    simp [volume]
                    simp_rw [my_haar_eq_count]
                    apply le_refl
                  . simp
                . simp
              .
                simpa using S_nonempty

              -- Finset.single_le_sum
            . simp
              grind
            .
              apply MeasureTheory.Integrable.of_integral_ne_zero
              rw [← g_inner_laplace]
              simp [G'_n]
              have foo := g_n_conv_norm (seq (n) + 1) (by simp) f_n_limit
              grind
        .
          exact NNReal.coe_nonneg _
      .
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← my_add_haar_eq_count]
          apply Lp.memLp
        . rw [← my_add_haar_eq_count]
          apply Lp.memLp
      .
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← my_add_haar_eq_count]
          apply Lp.memLp
        .
          refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
          rw [← my_add_haar_eq_count]
          rw [← neg_one_smul ℝ]
          rw [conv_smul]
          simp
          rw [← Pi.neg_def]
          simp [Conv]
          rw [← Function.comp_def (β := Additive G)]
          rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := Measure.count)]
          .
            conv =>
              arg 1
              arg 1
              arg 1
              equals ↑↑(G_n ((seq (n)) + 1) (by simp) f_n_limit) ∘ Additive.toMul =>
                rfl

            conv =>
              arg 1
              arg 1
              arg 2
              equals (delta y⁻¹) ∘ Additive.toMul =>
                rfl

            rw [← my_add_haar_eq_count]
            grw [ENNReal.eLpNorm_convolution_le_enorm_mul (p := 2) (q := 1)]
            .
              refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ?_) ?_
              · exact MeasureTheory.MemLp.eLpNorm_lt_top (MeasureTheory.MemLp.comp_measurePreserving (ν := volume) (Lp.memLp _) measure_preserving_unop_tomul)
              · refine MeasureTheory.MemLp.eLpNorm_lt_top (MeasureTheory.MemLp.comp_measurePreserving (ν := volume) ?_ measure_preserving_unop_tomul)
                apply Continuous.memLp_of_hasCompactSupport
                · fun_prop
                · simp [HasCompactSupport, tsupport]
            . simp
            . simp
            . simp
            . simp
            . apply AEMeasurable.of_discrete
            . apply AEMeasurable.of_discrete
          . apply AEStronglyMeasurable.of_discrete
          . rw [my_add_haar_eq_count]
            apply MeasurePreserving.id
    . rw [← my_haar_eq_count]
      apply Lp.memLp
    . rw [← my_haar_eq_count]
      simp
      apply MemLp.neg
      apply Lp.memLp
    . simp

  -- Now rename Hn ∗Gn such that we have added a constant so that Hn ∗Gn(e) = 0
  let new_seq: ℕ → ℕ := seq
  let H_G_conv_zero (n: ℕ) (g: G) := ((Conv (H_n ((new_seq n)) s) (G_n ((new_seq n) + 1) (by simp) f_n_limit)) g) - (Conv (H_n ((new_seq n)) s) (G_n ((new_seq n) + 1) (by simp) f_n_limit) 1)


  -- TODO - can the lipschitz constant can be improved?
  have H_G_conv_zero_lipschitz: ∀ n: ℕ, LipschitzWith ((((2 * #(S))^((2 : ℝ)⁻¹))) + 0) (H_G_conv_zero n) := by
    intro n
    simp only [H_G_conv_zero]
    simp only [new_seq]
    apply LipschitzWith.sub
    .
      apply h_n_f_lipschitz
    . apply LipschitzWith.const


  have H_n_conv_zero_eq: ∀ n: ℕ, (H_G_conv_zero (n) 1) - (H_G_conv_zero (n) s⁻¹) = ‖(G_n ((new_seq n) + 1) (by simp) f_n_limit) - (conv_finsupp_lp2 (((G_n ((new_seq n) + 1) (by simp) f_n_limit))) (delta s) (by simp [delta]))‖ := by
    intro n
    simp [H_G_conv_zero]
    have s_inv_eq: s⁻¹ = s⁻¹ * 1 := by
      simp
    rw [s_inv_eq]
    rw [← f_conv_delta  (f := Conv ((H_n ((new_seq n)) s)) ((G_n ((new_seq n) + 1) (by simp) f_n_limit)))]
    rw [← Pi.sub_apply]
    rw [sub_eq_add_neg]
    rw [← neg_one_smul ℝ]
    rw [← conv_smul]
    rw [ ← smul_conv]
    rw [conv_assoc_of_lp2]
    .
      rw [← conv_add_right]
      .
        simp [H_n, conv_finsupp_lp2]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_smul _ _)]
        rw [conv_smul]
        conv =>
          lhs
          lhs
          arg 0
          unfold Conv

        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)]
        simp only [convolution,
          ContinuousLinearMap.coe_sub', ContinuousLinearMap.mul_apply', Pi.smul_apply, smul_eq_mul]
        simp
        have t_fake_inv: ∀ (t: G), (t: (Additive G))⁻¹ = -(Additive.ofMul t) := by
          intro t
          rfl

        simp [t_fake_inv, Additive.ofMul]
        have one_g_eq: (1 : G) = (0 : (Additive G)) := rfl
        simp_rw [one_g_eq]
        simp_rw [zero_sub]
        conv =>
          lhs
          rhs
          arg 2
          intro t
          rhs
          rhs
          equals (conv_finsupp_lp2 (-(G_n (new_seq n + 1) (by simp) f_n_limit)) (delta s) (by simp [delta])) (-t) =>
            simp [conv_finsupp_lp2]
            simp_rw [tolp_apply]
            norm_cast
            rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_neg _)]

        simp [conv_finsupp_lp2]
        norm_cast
        simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_neg _)]
        simp_rw [← neg_one_smul (R := ℝ) (M := G → ℝ)]
        simp_rw [conv_smul]
        simp
        rw [MeasureTheory.MemLp.toLp_neg (by
          rw [f_conv_delta_helper]
          rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
          . apply MeasureTheory.Lp.memLp
          .
            exact measurePreserving_mul_left volume s⁻¹
        )]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_neg _)]
        simp_rw [← Pi.sub_apply]
        have real_inner: ∀ a b : ℝ, ⟪a, b⟫ = a * b := fun a b => by
          rw [show (⟪a, b⟫ : ℝ) = b * a from rfl, mul_comm]
        conv =>
          lhs
          rhs
          arg 2
          intro t
          rw [← Pi.add_apply]
          rw [← Pi.mul_apply]


        rw [MeasureTheory.integral_neg_eq_self]
        simp_rw [Pi.mul_apply]
        simp_rw [← real_inner]
        conv =>
          lhs
          rhs
          equals ‖(G_n (new_seq n + 1) (by simp) f_n_limit) - (MemLp.toLp (Conv ((G_n ((new_seq n) + 1) (by simp) f_n_limit)) (delta s)) (by
              rw [f_conv_delta_helper]
              rw [← Function.comp_def]
              apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
              . apply MeasureTheory.Lp.memLp
              .
                exact measurePreserving_mul_left volume s⁻¹
            ))‖^2 =>
            rw [← real_inner_self_eq_norm_sq]
            rw [MeasureTheory.L2.inner_def]
            simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
            rfl

        rw [pow_two]
        rw [real_inner]
        have key : ∀ a : ℝ, a⁻¹ * (a * a) = a := by
          intro a
          rcases eq_or_ne a 0 with h | h
          · simp [h]
          · field_simp
        exact key _
      .
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          . simp [volume]
            rw [my_haar_eq_count]
            apply MeasureTheory.MeasurePreserving.id
        .
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          . simp [volume]
            rw [my_haar_eq_count]
            apply MeasureTheory.MeasurePreserving.id
      .
        -- TODO - deduplicate this
        simp [f_conv_delta_helper]
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          . simp [volume]
            rw [my_haar_eq_count]
            apply MeasureTheory.MeasurePreserving.id
        .
          apply MeasureTheory.MemLp.neg
          rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          .
            simp [volume]
            rw [my_haar_eq_count]
            refine MeasurePreserving.mul_left Measure.count s⁻¹ ?_
            apply MeasureTheory.MeasurePreserving.id
    . rw [← my_haar_eq_count]
      apply Lp.memLp
    . rw [← my_haar_eq_count]
      simp
      apply MemLp.neg
      apply Lp.memLp
    . simp [delta]


  have compact_with_fixed_g (g: G): IsCompact (closure ( (Set.range (fun n => H_G_conv_zero n g)))) := by

    apply Bornology.IsBounded.isCompact_closure
    rw [Metric.isBounded_iff]
    use 2 * ((↑(#S) * 2) ^ (2 : ℝ)⁻¹) * (dist g 1)
    intro x hx y hy
    simp at hx
    simp at hy

    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy

    rw [← ha, ← hb]


    have foo := (H_G_conv_zero_lipschitz a).dist_le_mul g 1
    have bar := (H_G_conv_zero_lipschitz b).dist_le_mul g 1
    grw [dist_triangle (y := (H_G_conv_zero a) 1)]
    grw [foo]
    grw [dist_triangle (y := (H_G_conv_zero b) 1)]
    rw [dist_comm] at bar
    grw [bar]
    simp [H_G_conv_zero]
    ring
    simp

  have new_compact_closure: IsCompact (closure (Set.range (fun n => H_G_conv_zero n))) := by
    rw [Pi.isCompact_closure_iff]
    intro g
    apply Bornology.IsBounded.isCompact_closure
    rw [Metric.isBounded_iff]
    use 2 * ((↑(#S) * 2) ^ (2 : ℝ)⁻¹) * (dist g 1)
    intro x hx y hy
    simp at hx
    simp at hy

    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy

    rw [← ha, ← hb]

    have foo := (H_G_conv_zero_lipschitz a).dist_le_mul g 1
    have bar := (H_G_conv_zero_lipschitz b).dist_le_mul g 1
    grw [dist_triangle (y := (H_G_conv_zero a) 1)]
    grw [foo]
    grw [dist_triangle (y := (H_G_conv_zero b) 1)]
    rw [dist_comm] at bar
    grw [bar]
    simp [H_G_conv_zero]
    ring
    simp

  have arzela_tendsto := IsCompact.tendsto_subseq new_compact_closure (x := fun n => (
    H_G_conv_zero n
  )) (by
    intro n
    apply _root_.subset_closure
    simp
  )
  obtain ⟨arzela_lim, arzela_lim_mem, arzela_seq, arzela_seq_mono, tendsto_arzela_lim⟩ := arzela_tendsto
  rw [tendsto_pi_nhds] at tendsto_arzela_lim

  have tendsto_one := tendsto_arzela_lim 1
  have tendsto_s_inv := tendsto_arzela_lim s⁻¹
  simp at tendsto_one
  simp at tendsto_s_inv

  have abs_tendsto : ∀ z: ℝ, Filter.Tendsto (fun x => |x|) (nhds z) (nhds |z|)  := by
    intro z
    apply Continuous.tendsto
    fun_prop

  have tendsto_sub := tendsto_one.sub tendsto_s_inv
  use {
    toFun := fun g => arzela_lim g
    lipschitz := by
      use ⟨(((↑(#S) * 2) ^ (2 : ℝ)⁻¹)), by positivity⟩
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq]

      have new_tendsto_sub := (abs_tendsto _).comp ((tendsto_arzela_lim x).sub (tendsto_arzela_lim y))
      have sub_le := le_of_tendsto new_tendsto_sub (b := ((↑(#S) * 2) ^ (2 : ℝ)⁻¹) * (dist x y)) ?_
      . norm_cast
        norm_cast at sub_le
      . apply Filter.Eventually.of_forall
        intro n
        have foo := (H_G_conv_zero_lipschitz (arzela_seq n)).dist_le_mul x y
        rw [Real.dist_eq] at foo
        simp
        norm_cast
        simp at foo
        norm_cast at foo
        ring_nf at foo
        ring_nf
        exact foo

    harmonic := by
      simp [Harmonic]
      intro x
      rw [← sub_eq_zero]

      have sum_lim := tendsto_finset_sum (s := S) (fun s hs => tendsto_arzela_lim (s * x))
      have tendsto_sub := (tendsto_arzela_lim x).sub (sum_lim.const_mul ((#S : ℝ))⁻¹)
      norm_cast

      have lim_zero := squeeze_zero (t₀ := Filter.atTop)
        (f := (fun x_1 ↦ |((fun n ↦ H_G_conv_zero n) ∘ arzela_seq) x_1 x - (↑(#S))⁻¹ * ∑ c ∈ S, ((fun n ↦ H_G_conv_zero n) ∘ arzela_seq) x_1 (c * x)|))
        (g := fun n => (1 / (n + 1)))
        ?_ ?_ ?_
      .
        have target_eq_zero := tendsto_nhds_unique ((abs_tendsto _).comp tendsto_sub) (lim_zero)
        rw [abs_eq_zero] at target_eq_zero
        rw [sub_eq_zero] at target_eq_zero
        simp [target_eq_zero]
      . simp
      . intro n
        simp
        conv =>
          lhs
          arg 1
          equals Laplace_b (H_G_conv_zero (arzela_seq n)) x =>
            simp [Laplace_b]
            simp [f_conv_mu]


        have ae_le := ENNReal.ae_le_essSup (fun x ↦ ENNReal.ofReal |Laplace_b (H_G_conv_zero (arzela_seq n)) x|) (μ := volume)
        simp [volume] at ae_le
        rw [my_haar_eq_count] at ae_le
        rw [count_ae_everywhere] at ae_le
        specialize ae_le x
        rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]
        grw [ae_le]

        simp [H_G_conv_zero]
        intro i
        rw [← Pi.sub_def]
        rw [laplace_b_sub]
        simp
        rw [sub_eq_add_neg]
        grw [abs_add_le]
        simp
        rw [laplace_conv_eq_laplace_right_of_lp2]
        .
          simp [Conv]
          grw [ENNReal.ofReal_add_le]
          rw [← Real.enorm_eq_ofReal_abs]
          grw [counting_le_essSup]
          rw [essSup_eq_elpNorm_top]
          simp only [volume]
          simp_rw [haar_eq_haar_add]
          conv =>
            lhs
            arg 1
            arg 1
            arg 2
            equals (Laplace_b (G_n ((new_seq (arzela_seq n)) + 1) (by simp) f_n_limit)) ∘ Additive.toMul =>
              rfl

          conv =>
            lhs
            arg 1
            arg 1
            arg 1
            equals (H_n (new_seq (arzela_seq n)) s) ∘ Additive.toMul =>
              rfl

          refine le_trans (add_le_add_left (ENNReal.eLpNorm_convolution_le_enorm_mul (G := Additive G) (L := ContinuousLinearMap.mul ℝ ℝ) (p := 2) (q := 2) (r := ⊤) (μ := myHaarAddOpp) ?_ ?_ ?_ ?_ ?_ ?_) _) ?_
          · simp
          · simp
          · simp
          · rw [ENNReal.inv_top, zero_add]; exact ENNReal.inv_two_add_inv_two
          · apply AEMeasurable.of_discrete
          · apply AEMeasurable.of_discrete
          .
            conv =>
              lhs
              arg 1
              arg 1
              arg 2
              arg 1
              equals ↑↑(H_n (seq (arzela_seq n)) s) => rfl


            rw [show eLpNorm (↑↑(H_n (seq (arzela_seq n)) s)) 2 myHaarAddOpp = 1 from by
                  have h := H_n_norm (arzela_seq n)
                  rw [MeasureTheory.Lp.enorm_def] at h
                  rw [my_add_haar_eq_count,
                      show (Measure.count : Measure (Additive G)) = myHaar from my_haar_eq_count.symm]
                  exact h]
            simp [enorm]
            have g_norm := g_n_laplace_enorm_le (seq (arzela_seq n) + 1) (by simp) f_n_limit
            rw [MeasureTheory.Lp.enorm_def] at g_norm
            simp only [Laplace] at g_norm
            rw [laplace_b_const]
            simp [Laplace_b]
            rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)] at g_norm
            simp only [conv_mu_lp2] at g_norm
            rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at g_norm
            refine le_trans (le_of_eq (eLpNorm_comp_measurePreserving (by apply AEStronglyMeasurable.of_discrete) measure_preserving_unop_tomul)) ?_
            grw [g_norm]
            norm_cast
            simp
            norm_cast
            rw [ENNReal.ofReal_inv_of_pos (by positivity)]
            simp
            norm_cast
            have seq_le_n : n ≤ seq (arzela_seq n) := by
              have n_arzela : n ≤ arzela_seq n := by
                apply StrictMono.le_apply arzela_seq_mono
              apply LE.le.trans n_arzela

              apply StrictMono.le_apply seq_mono

            omega

        .
          -- TODO - deduplicate this
          simp [ConvExists]
          rw [my_add_haar_eq_count]
          apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
          . infer_instance
          . simp
          . apply AEStronglyMeasurable.of_discrete
          . apply AEStronglyMeasurable.of_discrete
          . rw [← Function.comp_def]
            apply MeasureTheory.MemLp.comp_measurePreserving
            . apply Lp.memLp
            . simp [volume]
              rw [my_haar_eq_count]
              apply MeasureTheory.MeasurePreserving.id
          .
            apply MeasureTheory.MemLp.comp_measurePreserving
            . apply Lp.memLp
            . simp [volume]
              rw [my_haar_eq_count]
              apply MeasureTheory.MeasurePreserving.id
        . rw [← my_haar_eq_count]
          apply Lp.memLp
        . rw [← my_haar_eq_count]
          apply Lp.memLp
      .
        simp
        simp_rw [inv_eq_one_div]
        apply tendsto_one_div_add_atTop_nhds_zero_nat
  }
  intro z
  by_contra!
  have lim_ge := ge_of_tendsto tendsto_sub (b := 1) (by
    apply Filter.Eventually.of_forall
    intro n
    rw [H_n_conv_zero_eq]
    simp [new_seq, seq]
    have norm_gt := Nat.nth_mem_of_infinite s_infinite ((arzela_seq n))
    simp at norm_gt
    apply le_of_lt
    exact norm_gt
  )

  apply_fun (fun f => f 1 - f s⁻¹) at this
  simp [ConstLipschitzH] at this
  norm_cast at this
  grind


-- Case two of Theorem 3.6

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Harmonic
attribute [-instance] _root_.GeneratesNS.T2_W _root_.GeneratesNS.const_isClosed _root_.GeneratesNS.proper_linear_w _root_.GeneratesNS.rho_g_FG _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Existence of a nontrivial harmonic function

`nontrivial_harmonic_case_two` and the main result `exists_nontrivial_harmonic`.

Root of the `Gromov.Harmonic` hierarchy.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

open scoped RealInnerProductSpace

set_option maxHeartbeats 2000000 in
lemma nontrivial_harmonic_case_two (f_n_limit: ∃ s: S, ¬(Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0))): ∃ F: LipschitzH , ∀ z: ℝ, F ≠ ConstLipschitzH z := by
  obtain ⟨s, hs⟩ := f_n_limit
  let H_n := fun n g => if  ((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹) ≠ 0 then ((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹) / |((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹)| else 1

  -- TODO - why can't we write '∞' here
  have H_n_norm: ∀ n: ℕ, MeasureTheory.eLpNorm (H_n n) (p := ⊤) MeasureTheory.volume = 1 := by
    intro n
    simp [H_n]
    simp [MeasureTheory.eLpNormEssSup]
    simp [MeasureTheory.volume]
    rw [my_haar_eq_count]
    simp
    have h_norm_one: ∀ x, ‖H_n n x‖ₑ = 1 := by
      simp [H_n]
      intro g
      split_ifs
      . simp
      .

        rename_i foo
        by_cases val_pos: 0 ≤ ((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹)
        .
          rw [abs_of_nonneg val_pos]
          rw [div_self]
          . simp
          . exact foo
        .
          rw [abs_of_neg]
          .
            rw [div_neg_self]
            .
              simp
            . exact foo
          . linarith

    unfold H_n at h_norm_one
    simp at h_norm_one
    simp_rw [h_norm_one]
    simp

  have H_n_diff_pos: ∀ n: ℕ,  ∀ (i : G), 0 ≤ H_n n i⁻¹ * f_n n i - H_n n i⁻¹ * f_n n ((↑s)⁻¹ * i) := by
    intro n g
    simp [H_n]
    simp [f_conv_delta]
    split_ifs
    . linarith
    .
      rename_i diff_zero
      by_cases val_pos: 0 ≤ f_n n g - f_n n ((↑s)⁻¹ * g)
      .
        rw [abs_of_nonneg val_pos]
        rw [div_self]
        . linarith
        . assumption
      .
        rw [abs_of_neg]
        . rw [div_neg_self]
          . linarith
          . assumption
        .
          simpa using val_pos

  have fn_sub_norm: ∀ n: ℕ, eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 = ENNReal.ofReal |((Conv (H_n n) (f_n n)) 1) - ((Conv (H_n n) (f_n n)) s⁻¹)| := by
    intro n
    simp [eLpNorm, eLpNorm']
    rw [lintegral_g_eq_add]
    conv =>
      lhs
      arg 1
      intro g
      rw [Real.enorm_eq_ofReal_abs]
      arg 1
      equals (H_n n g⁻¹) * (f_n n g - (Conv (f_n n) (delta s.val)) g) =>
        simp [H_n]
        split_ifs
        .
          rename_i diff_eq_zero
          simp [diff_eq_zero]
        .
          rename_i diff_ne_zero
          by_cases val_pos: 0 ≤ ((f_n n g) - (Conv (f_n n) (delta s.val)) g)
          .
            rw [abs_of_nonneg]
            .
             rw [div_self]
             simp
             apply diff_ne_zero
            . exact val_pos
          .
            rw [abs_of_neg]
            .
              rw [div_neg_self]
              simp
              exact diff_ne_zero
            .
              simpa using val_pos

    rw [conv_eq_sum (by
      apply conv_exists_fin_supp
      right
      unfold f_n
      simp
      apply Set.Finite.inter_of_right
      apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
      refine Set.Finite.biUnion' ?_ ?_
      . exact Set.toFinite (Membership.mem Finset.univ.val)
      . intro m hm
        apply mu_conv_finsupp
    )]

    rw [conv_eq_sum (by
      apply conv_exists_fin_supp
      right
      unfold f_n
      simp
      apply Set.Finite.inter_of_right
      apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
      refine Set.Finite.biUnion' ?_ ?_
      . exact Set.toFinite (Membership.mem Finset.univ.val)
      . intro m hm
        apply mu_conv_finsupp
    )]


    conv =>
      rhs
      arg 1
      arg 1
      rw [← Summable.tsum_sub (by
        apply summable_of_hasFiniteSupport
        change (Function.support _).Finite
        simp only [Function.support_mul]
        apply Set.Finite.inter_of_right
        unfold f_n
        simp
        apply Set.Finite.inter_of_right
        apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
        refine Set.Finite.biUnion' ?_ ?_
        . exact Set.toFinite (Membership.mem Finset.univ.val)
        .
          intro m hm
          apply Set.Finite.of_injOn (f := fun a => ((Additive.toMul a))⁻¹) (ht := mu_conv_finsupp  m)
          .
            intro a ha
            exact ha
          . intro a ha b hb
            simp
      ) (by
        apply summable_of_hasFiniteSupport
        change (Function.support _).Finite
        simp only [Function.support_mul]
        apply Set.Finite.inter_of_right
        unfold f_n
        simp
        apply Set.Finite.inter_of_right
        apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
        refine Set.Finite.biUnion' ?_ ?_
        . exact Set.toFinite (Membership.mem Finset.univ.val)
        .
          intro m hm
          apply Set.Finite.of_injOn (f := fun a => s.val⁻¹ * ((Additive.toMul a))⁻¹ ) (ht := mu_conv_finsupp  m)
          .
            intro a ha
            exact ha
          . intro a ha b hb
            simp
      )]
    simp_rw [mul_sub]
    simp_rw [f_conv_delta]
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    rw [ENNReal.ofReal_eq_ofReal_iff]
    rw [← Function.Injective.tsum_eq (γ := G) (β := Additive (G)) (g := fun a => Additive.ofMul (a⁻¹))]
    simp
    rw [abs_of_nonneg]
    rfl
    .
      apply tsum_nonneg
      apply H_n_diff_pos n
    .
      simp
      apply Function.Injective.comp
      . exact neg_injective
      . exact fun ⦃a₁ a₂⦄ a ↦ a
    .
      simp
      intro g hg
      use g⁻¹
      simp
    .
      apply tsum_nonneg
      apply H_n_diff_pos n
    . simp
    . apply H_n_diff_pos n
    .
      simp_rw [← mul_sub]
      apply summable_of_hasFiniteSupport
      change (Function.support _).Finite
      simp only [Function.support_mul]
      apply Set.Finite.inter_of_right
      apply Set.Finite.subset (hs := ?_) (ht := Function.support_sub _ _)
      simp
      refine ⟨?_, ?_⟩
      . apply f_n_fin_supp
      .
        apply Set.Finite.of_injOn (f := fun a => s.val⁻¹ * a) (ht := f_n_fin_supp n)
        . intro a ha
          simpa using ha
        . simp


  have haar_eq_haar_add : myHaar = myHaarAddOpp := by
    rfl

  have h_conv_f_bounded (n: ℕ): eLpNorm (Conv (H_n n) (f_n n)) ⊤ ≤ 1 := by
    unfold Conv
    eta_reduce
    simp only [volume]
    rw [haar_eq_haar_add]
    have my_norm := ENNReal.eLpNorm_convolution_le_enorm_mul (f := H_n n) (G := (Additive G)) (L := (ContinuousLinearMap.mul ℝ ℝ))
      (g := f_n n) (r := ⊤) (p := ⊤) (q := 1) (μ := myHaarAddOpp)
      (by simp) (by simp) (by simp) (by simp)
      (by apply AEMeasurable.of_discrete)
      (by apply AEMeasurable.of_discrete)
    refine le_trans my_norm ?_
    have norm_one := f_n_norm_one (n )
    simp [volume] at norm_one
    rw [haar_eq_haar_add] at norm_one
    simp only  [volume] at H_n_norm
    rw [haar_eq_haar_add] at H_n_norm
    refine le_trans (mul_le_mul' (mul_le_mul' (show ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ ≤ 1 by simp [enorm]) (le_of_eq (H_n_norm n))) (le_of_eq norm_one)) ?_
    simp

  have conv_laplce_norm (n: ℕ): eLpNorm ((Laplace_b ((Conv (H_n n)) (f_n n)))) ⊤ (μ := volume (α := G)) ≤ eLpNorm (H_n n) ⊤ * (eLpNorm (Laplace_b (f_n n)) 1 (μ := volume (α := G))) := by
    rw [laplace_conv_eq_laplace_right]
    .
      unfold Conv
      eta_reduce
      simp only [volume]
      rw [haar_eq_haar_add]

      have my_norm := ENNReal.eLpNorm_convolution_le_enorm_mul (f := H_n n) (G := (Additive G)) (L := (ContinuousLinearMap.mul ℝ ℝ))
        (g := Laplace_b (f_n n)) (r := ⊤) (p := ⊤) (q := 1) (μ := myHaarAddOpp)
        (by simp)
        (by simp)
        (by simp)
        (by simp)
        (by apply AEMeasurable.of_discrete)
        (by apply AEMeasurable.of_discrete)


      refine le_trans my_norm ?_
      have h1 : ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ ≤ 1 := by simp [enorm]
      calc ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ * eLpNorm (H_n n) ⊤ myHaarAddOpp * eLpNorm (Laplace_b (f_n n)) 1 myHaarAddOpp
          ≤ 1 * eLpNorm (H_n n) ⊤ myHaarAddOpp * eLpNorm (Laplace_b (f_n n)) 1 myHaarAddOpp := by gcongr
        _ = eLpNorm (H_n n) ⊤ myHaarAddOpp * eLpNorm (Laplace_b (f_n n)) 1 myHaarAddOpp := by rw [one_mul]
    .
      apply conv_exists_fin_supp
      right
      exact f_n_fin_supp n
    . apply f_n_nonneg
    . exact f_n_fin_supp n


  let conv_h_n_cont (n: ℕ): C(G, ℝ) := {
    toFun := Conv (H_n n) (f_n n),
    continuous_toFun := by exact continuous_of_discreteTopology
  }

  have abs_conv_le_one: ∀ g: G, ∀ n: ℕ,  |Conv (H_n n) (f_n n) g| ≤ 1 := by
    intro g n
    have norm_bound := h_conv_f_bounded n
    simp [eLpNorm, eLpNormEssSup] at norm_bound
    have ae_le := ENNReal.ae_le_essSup (fun x ↦ ‖Conv (H_n n) (f_n n) x‖ₑ) (μ := volume)
    simp [volume] at ae_le
    rw [my_haar_eq_count] at ae_le
    rw [count_ae_everywhere] at ae_le
    simp_rw [Real.enorm_eq_ofReal_abs] at ae_le
    simp_rw [Real.enorm_eq_ofReal_abs] at norm_bound
    norm_cast at ae_le
    simp [volume] at norm_bound
    rw [my_haar_eq_count] at norm_bound
    specialize ae_le g
    have ennreal_bound := le_trans ae_le norm_bound
    norm_cast at ennreal_bound

  have conv_h_n_lipschitz (n: ℕ): LipschitzWith 2 (conv_h_n_cont n) := by
    unfold conv_h_n_cont
    simp [LipschitzWith]
    intro x y
    by_cases x_eq_y: x = y
    . simp [x_eq_y]
    .
      norm_cast
      rw [edist_dist]
      rw [Real.dist_eq]
      rw [edist_dist]
      conv =>
        rhs
        equals ENNReal.ofReal (2 * (dist x y)) =>
          rw [ENNReal.ofReal_mul]
          . simp
          . linarith
      rw [ENNReal.ofReal_le_ofReal_iff]
      .
        grw [abs_sub]
        grw [abs_conv_le_one x]
        grw [abs_conv_le_one y]
        rw [one_add_one_eq_two]
        simp
        simp [dist]
        have dist_ne_zero: dist x y ≠ 0 := by
          exact dist_ne_zero.mpr x_eq_y
        simp [dist] at dist_ne_zero
        omega
      . simp [dist]


  have compact_closure_f: IsCompact (closure ( (Set.range (fun n => (Conv (H_n n) (f_n n)))))) := by
    rw [Pi.isCompact_closure_iff]
    intro g
    apply Bornology.IsBounded.isCompact_closure
    rw [Metric.isBounded_iff]
    use 2
    intro x hx y hy
    simp at hx
    simp at hy
    obtain ⟨n, h_x_n⟩ := hx
    obtain ⟨m, h_y_m⟩ := hy
    rw [Real.dist_eq]
    grw [abs_sub]
    rw [← h_x_n, ← h_y_m]
    grw [abs_conv_le_one]
    grw [abs_conv_le_one]
    linarith


  rw [Filter.not_tendsto_iff_exists_frequently_notMem] at hs
  obtain ⟨eps, h_eps, frequently_gt_eps⟩ := hs
    -- We obtain a subsequence where all of the points satisfy the 'norm > ε' condition
  obtain ⟨eps_seq, mono_eps_seq, eps_seq_gt_x⟩ := Filter.extraction_of_frequently_atTop frequently_gt_eps

  -- Along this sequence, the evauation of 'Conv H_n f_n' at is leq to 1,
  -- so it's in a compact set


  have h_n_pointwise_converge := IsCompact.tendsto_subseq compact_closure_f (x := fun n => (Conv (H_n (eps_seq n)) (f_n (eps_seq n)))) (by
    intro n
    apply Set.mem_of_subset_of_mem (_root_.subset_closure)
    simp
  )
  -- We now have a sequence of functions which converges pointwise, where all of the
  -- elements of the sequence satisfy the 'norm > ε' condition
  obtain ⟨F, F_mem, seq, seq_mono, tendsto_F⟩ := h_n_pointwise_converge
  let F_lipschitzh := nontrivial_harmonic_common 2 (eps_seq ∘ seq) (by
    apply Filter.Tendsto.comp (x := Filter.atTop) (y := Filter.atTop)
    . exact StrictMono.tendsto_atTop mono_eps_seq
    . exact StrictMono.tendsto_atTop seq_mono
  ) F H_n conv_h_n_lipschitz tendsto_F H_n_norm
  use F_lipschitzh
  intro z
  have not_conv_tendsto_zero: ¬Filter.Tendsto (fun n => ENNReal.ofReal |Conv (H_n (eps_seq (seq n))) (f_n (eps_seq (seq n))) 1 - Conv (H_n (eps_seq (seq n))) (f_n (eps_seq (seq n))) (↑s)⁻¹|) Filter.atTop (nhds 0) := by
    rw [Filter.not_tendsto_iff_exists_frequently_notMem]
    use eps
    refine ⟨h_eps, ?_⟩
    simp_rw [← fn_sub_norm]
    apply Filter.Frequently.of_forall
    intro n
    exact eps_seq_gt_x (seq n)

  have F_non_const: F 1 ≠ F s⁻¹ := by
    by_contra!
    rw [← sub_eq_zero] at this
    rw [tendsto_pi_nhds] at tendsto_F
    have lim_f_sub := Filter.Tendsto.sub (tendsto_F 1) (tendsto_F s⁻¹)
    rw [this] at lim_f_sub
    simp_rw [Function.comp_def] at lim_f_sub
    rw [tendsto_zero_iff_abs_tendsto_zero] at lim_f_sub
    rw [Function.comp_def] at lim_f_sub
    have f_sub_ennreal := ENNReal.tendsto_ofReal lim_f_sub
    simp only [ENNReal.ofReal_zero] at f_sub_ennreal
    contradiction

  by_contra!
  -- TODO - there must be a cleaner way
  have app_one_eq: F_lipschitzh 1 = ConstLipschitzH z (1: G) := by
    rw [this]
  unfold F_lipschitzh ConstLipschitzH at app_one_eq
  simp [DFunLike.coe] at app_one_eq

  have app_s_inv_eq: F_lipschitzh s⁻¹ = ConstLipschitzH z (s⁻¹: G) := by
    rw [this]
  unfold F_lipschitzh ConstLipschitzH at app_s_inv_eq
  simp [DFunLike.coe] at app_s_inv_eq
  rw [← app_one_eq] at app_s_inv_eq
  norm_cast at app_s_inv_eq
  rw [eq_comm] at app_s_inv_eq
  simp [nontrivial_harmonic_common] at app_s_inv_eq
  contradiction


-- Theorem 3.6 - a non-constant harmonic function exists on G
theorem exists_nontrivial_harmonic: ∃ F: LipschitzH , ∀ z: ℝ, F ≠ ConstLipschitzH z := by
  by_cases f_n_limit: ∃ s: S, ¬(Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0))
  . exact nontrivial_harmonic_case_two f_n_limit
  .
    simp at f_n_limit
    exact nontrivial_harmonic_case_one (by
      intro s
      exact f_n_limit s.val s.property
    )

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.RhoAbelian
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# `rho_g` contains a finite-index abelian subgroup

`rho_g_contains_abelian`, the bundled input `Theorem3_1_Input`, and the infinite-image case.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped RealInnerProductSpace

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 9000000


lemma g_hom_abelian {T: Type*} [Group T] (A: Subgroup G) (A_finite_index: A.FiniteIndex) (hom: A →* T) (hom_surjective: Function.Surjective hom) (H: Subgroup T) (H_infinite: Infinite H) (H_abeliean: IsMulCommutative H) (H_finite_index: H.FiniteIndex) (H_FG: Group.FG H): Nonempty (Theorem3_1_Input G) := by
  -- TODO - generalize this to a lemma: finite-index subgroup of an infinite group is infinite
  -- and upstream to mathlib


  -- TODO - figure out how to make instance inference work here
  obtain ⟨i, j, i_fin, j_fin, p, p_prime, e, exists_iso⟩ := @CommGroup.equiv_free_prod_prod_multiplicative_zmod H (haveI := H_abeliean; { (inferInstance : Group H) with mul_comm := mul_comm' }) (H_FG)
  have iso := Classical.choice exists_iso

  have j_nonempty: Nonempty j := by
    by_contra!
    have H_finite : Finite H := by
      rw [Equiv.finite_iff iso.toEquiv]
      have finite_i: Finite i := by
        infer_instance
      have finite_mul: ∀ f: i, Finite (Multiplicative (ZMod (p f ^ e f))) := by
        intro f
        simp [Multiplicative]
        have pow_ne_zero: NeZero (p f ^ e f) := by
          exact {
            out := by
              simp
              have first_ne_zero := Nat.Prime.ne_zero (p_prime f)
              simp [first_ne_zero]
          }
        apply Finite.of_fintype
      apply Finite.instProd
    have no_finite := H_infinite.not_finite
    contradiction

  -- TODO - can we get the comp '∘' syntax to give us a monoid hom, instead of a plain function?
  let h_to_z := (Pi.evalMonoidHom _ (Classical.choice (by
    exact j_nonempty
  ))).comp ((MonoidHom.fst _ _).comp iso.toMonoidHom)

  have h_to_z_surjective: Function.Surjective h_to_z := by
    unfold h_to_z
    simp
    apply Function.Surjective.comp
    .
      intro x
      simp
      use fun _ => x
    . apply Function.Surjective.comp
      . exact Prod.fst_surjective
      . exact iso.surjective


  let G' := Subgroup.comap hom H

  -- TODO - generalize this and PR to mathlib


  have G'_finite_index: G'.FiniteIndex := by
    unfold G'
    exact {
      index_ne_zero := by
        simp
        rw [Subgroup.index_comap]
        -- apply somehow found this - how does it work???
        exact Subgroup.FiniteIndex.index_ne_zero
    }


  -- TODO - there must be an easier way to do this
  let g'_to_h: (map A.subtype G') →* H := {
    toFun := fun g => ⟨hom ⟨g.val, by (
      -- TODO - clean this up
      have foo := g.property
      rw [Subgroup.mem_map] at foo
      obtain ⟨x, hx, a_subtype⟩ := foo
      rw [← a_subtype]
      simp
    )⟩, by (
      have g_prop := g.property
      simp only [G', Subgroup.mem_comap] at g_prop
      rw [Subgroup.mem_map] at g_prop
      obtain ⟨x, hx, a_subtype⟩ := g_prop
      simp_rw [← a_subtype]
      simp
      simp at hx
      exact hx
    )⟩
    map_one' := by
      simp
      conv =>
        lhs
        arg 2
        equals 1 => simp
      simp

    map_mul' := by
      simp
      intro a ha a_mem b hb b_mem

      conv =>
        lhs
        arg 2
        equals ⟨a, ha⟩ * ⟨b, hb⟩ => simp
      rw [MonoidHom.map_mul]
  }

  let additive_g'_to_h := g'_to_h.toAdditive
  let additive_h_to_z := h_to_z.toAdditive

  let g_to_additive_z := additive_h_to_z.comp additive_g'_to_h
  let g_to_z := (AddEquiv.additiveMultiplicative ℤ).toAddMonoidHom.comp g_to_additive_z


  apply Nonempty.intro
  exact {
    G' := Subgroup.map A.subtype G',
    finite_index := by
      rw [Subgroup.finiteIndex_iff]
      simp [Subgroup.index_map_subtype]
      refine ⟨?_, ?_⟩
      . rw [← ne_eq]
        rw [← Subgroup.finiteIndex_iff]
        exact G'_finite_index
      . exact A_finite_index.index_ne_zero
      -- G'_finite_index
    φ := g_to_z,
    hφ := by
      simp [g_to_z, g_to_additive_z]
      apply Function.Surjective.comp
      . simp [additive_h_to_z]
        exact h_to_z_surjective
      .
        simp [additive_g'_to_h, g'_to_h]
        intro h
        obtain ⟨a, hom_a⟩ := hom_surjective h
        simp
        use a
        simp
        simp [G', hom_a]
  }

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Theorem31Input
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Constructing a `Theorem3_1_Input`

The finite-image case `rho_g_case_finite` and `exists_theorem_3_1_input`.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped RealInnerProductSpace

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 9000000

open MeasureTheory

open MeasureTheory

-- TODO - figure out why we need these


omit hGS in
lemma rangeRestrict_range {A B: Type*} [Group A] [Group B] (f: A →* B): f.rangeRestrict.range = ⊤ := by
  ext a
  have a_prop := a.property
  simp only [mem_top, iff_true]
  rw [MonoidHom.mem_range] at a_prop
  rw [MonoidHom.mem_range]
  obtain ⟨x, hx⟩ := a_prop
  use x
  ext
  simp [hx]


lemma rho_g_case_finite_oai (hr: Finite (↥(rho_g))): Nonempty (Theorem3_1_Input G) := by
  unfold rho_g at hr

  have ker_finite_index := Subgroup.finiteIndex_ker (GRepW_base)
  let G' := (GRepW_base).ker

  let G'_action := (GRepW_base).domRestrict G'

  have act_ker (g: G) := MonoidHom.mem_ker (f := (GRepW_base)) (x := g)

  have act_v (g: G) (hg: g ∈ (GRepW_base).ker) (f: LipschitzH ): Submodule.Quotient.mk (GRep  g f) = (Submodule.Quotient.mk (f) : W) := by
    simp [GRep]
    have apply_g := (act_ker g).mp hg
    simp [GRepW_base, GRepW_non_invertible, GRep] at apply_g
    apply_fun Units.val at apply_g
    rw [Representation.asGroupHom_apply] at apply_g
    rw [Representation.quotient_apply] at apply_g
    apply_fun (fun y => y (Submodule.Quotient.mk f)) at apply_g
    simp at apply_g
    exact apply_g

  let extract_const (f: LipschitzH) (hf: f ∈ ConstF ) := f 1

  simp_rw [Submodule.Quotient.eq] at act_v

  -- As proved in 'act_v', we have  '(GRep g f) - f' is a constant function. We can therefore evaluate
  -- it any poitn in G (here, 1) to get the constant
  let lambda_g := fun (g: G') (f: LipschitzH ) => ((GRep g.val) f - f) 1
  let lambda_g_dual (g: G'): Module.Dual ℝ (LipschitzH) := {
    toFun := fun w => lambda_g g w
    map_add' := by
      intro x y
      simp [lambda_g]
      abel
    map_smul' := by
      intro c x
      simp [lambda_g]
      rw [mul_sub]
  }

  -- TODO - this could be much cleaner
  have act_eq_lambda (g: G) (hg: g ∈ (GRepW_base).ker) (f: LipschitzH ): (gAct g f) = f + ConstLipschitzH (lambda_g ⟨g, hg⟩ f) := by
    have act := act_v g hg f
    simp [GRep, gAct, ConstF] at act
    simp [gAct]
    obtain ⟨y, hy⟩ := act
    simp [lambda_g, GRep, gAct]
    ext a
    simp
    apply_fun (fun l => l.toFun) at hy
    have app_a := congrFun hy a
    simp [lipschitz_sub_tofun] at app_a
    rw [eq_comm] at app_a
    apply eq_add_of_sub_eq at app_a
    rw [app_a]
    rw [add_comm]
    simp [LipschitzH_apply]
    simp [LipschitzH_apply] at hy
    have other_app := congrFun hy 1
    simp at other_app
    rw [← other_app]
    simp [ConstLipschitzH]

  have lambda_const (g: (GRepW_base).ker) (f: LipschitzH ) (k: ℝ): (lambda_g g (f + (ConstLipschitzH k))) = (lambda_g g f) := by
    simp [lambda_g, GRep, gAct]
    simp [ConstLipschitzH]


  let lambda_g_hom: G' →* Multiplicative (Module.Dual ℝ (LipschitzH)) := {
    toFun := fun g => Multiplicative.ofAdd (lambda_g_dual g)
    map_one' := by
      simp [lambda_g_dual]
      simp [lambda_g]
      ext f
      simp
    map_mul' := by
      intro g h
      ext f
      simp [lambda_g_dual]
      conv =>
        lhs
        dsimp [lambda_g]
      simp [GRep]
      rw [gAct_mul]
      rw [act_eq_lambda h.val h.property]
      rw [act_eq_lambda g.val g.property]
      rw [lambda_const]
      simp [ConstLipschitzH]
      group
  }

  by_cases lambda_g_infinite: Infinite (lambda_g_hom.range)
  .

    apply g_hom_abelian G' ?_ lambda_g_hom.rangeRestrict ?_ lambda_g_hom.rangeRestrict.range ?_ ?_ ?_ ?_
    . simp [G']
      exact ker_finite_index
    . exact MonoidHom.rangeRestrict_surjective lambda_g_hom
    . rw [rangeRestrict_range]
      simp
      -- TODO: PR this to mathlib
      apply (Equiv.infinite_iff (α := lambda_g_hom.range) _).mp
      . exact lambda_g_infinite
      . exact {
          toFun := fun g => ⟨g, trivial⟩
          invFun := fun g => g.val
          left_inv := by simp [Function.LeftInverse]
          right_inv := by simp [Function.RightInverse, Function.LeftInverse]
        }
    . exact {
        is_comm := {
          comm := by
            intro a b
            ext
            simp
            rw [add_comm]
        }
      }
    . rw [Subgroup.finiteIndex_iff]
      rw [rangeRestrict_range]
      simp
    . rw [rangeRestrict_range]
      simp
      exact Group.FG.out
  .
    simp only [not_infinite_iff_finite] at lambda_g_infinite
    let G'' := lambda_g_hom.ker
    have G''_finite_index := Subgroup.finiteIndex_ker lambda_g_hom

  -- TODO - this could be a lot cleaner
    have G''_act_v (g: lambda_g_hom.ker) (x: G) (f: LipschitzH ): f (x * g) = f x := by
      specialize act_v g
      simp at act_v
      have g_prop := g.property
      rw [MonoidHom.mem_ker] at g_prop
      simp [lambda_g_hom, lambda_g_dual, lambda_g, GRep] at g_prop
      apply_fun (fun p => p f) at g_prop
      simp at g_prop
      rw [sub_eq_zero] at g_prop
      simp [gAct] at g_prop
      specialize act_v f
      simp [GRep, gAct, ConstF] at act_v
      obtain ⟨y, hy⟩ := act_v
      simp [ConstLipschitzH] at hy
      apply_fun (fun l => l.toFun) at hy
      simp at hy
      rw [Pi.sub_def] at hy
      have eval_one := hy
      apply_fun (fun f => f 1) at eval_one
      apply_fun (fun f => f x) at hy
      simp at hy
      simp at eval_one
      rw [← g_prop] at eval_one
      simp at eval_one
      rw [eq_comm] at hy
      apply eq_add_of_sub_eq' at hy
      simp
      rw [hy]
      simp
      exact eval_one


    -- View G'' as a subgroup of G
    let G''_subgroup_G := (Subgroup.map G'.subtype lambda_g_hom.ker)

    -- TODO - clean up this proof
    have G''_subgroup_finite_index: G''_subgroup_G.FiniteIndex := by
      unfold G''_subgroup_G
      rw [Subgroup.finiteIndex_iff]
      rw [Subgroup.index_map]
      simp
      unfold G'
      rw [Subgroup.finiteIndex_iff] at ker_finite_index
      refine ⟨?_, ker_finite_index⟩
      rw [Subgroup.finiteIndex_iff] at G''_finite_index
      exact G''_finite_index


    have finite_quotient := Subgroup.finite_quotient_of_finiteIndex (H := G''_subgroup_G)

    have coset_union := QuotientGroup.univ_eq_iUnion_smul G''_subgroup_G
    have f_range_eq (f: LipschitzH ): Set.range f = Set.range ((fun (x: G ⧸ G''_subgroup_G) => f (x.out))) := by
      ext a
      refine ⟨?_, ?_⟩
      . intro ha
        simp at ha
        obtain ⟨y, hy⟩ := ha
        have y_mem: y ∈ Set.univ := by simp
        rw [coset_union] at y_mem
        simp at y_mem
        obtain ⟨i, hi⟩ := y_mem
        rw [Set.mem_smul_set] at hi
        obtain ⟨x, x_mem, y_eq⟩ := hi
        rw [← y_eq] at hy

        unfold G''_subgroup_G at x_mem
        simp at x_mem
        obtain ⟨x_mem_g', hx'⟩ := x_mem

        have x_mem_ker: ⟨x, x_mem_g'⟩ ∈ lambda_g_hom.ker := by
          simp
          exact hx'

        let x_ker: lambda_g_hom.ker := ⟨⟨x, x_mem_g'⟩, x_mem_ker⟩
        have f_translate := G''_act_v x_ker i.out f

        simp only [Set.mem_range]
        use i
        rw [← f_translate]
        exact hy
      . intro ha
        simp only [Set.mem_range] at ha
        obtain ⟨y, hy⟩ := ha
        simp
        simp at hy
        use y.out


    have all_f_const (f: LipschitzH ): ∃ z: ℝ, f = ConstLipschitzH z := by
      have f_max := Set.Finite.exists_maximalFor (fun y => ‖y‖) (Set.range f) ?_ ?_
      obtain ⟨z, z_mem, hz⟩ := f_max

      have z_max: ∀ p ∈ Set.range f, ‖p‖ ≤ ‖z‖ := by
        intro p hp
        simp at hp
        obtain ⟨y, hy⟩ := hp
        by_cases p_le_z: ‖p‖ ≤ ‖z‖
        . exact p_le_z
        . simp at p_le_z

          have f_le := hz (j := f.toFun y) ?_ ?_
          .
            simp at f_le
            rw [← hy]
            exact f_le
          . simp
          . simp
            rw [← hy] at p_le_z
            linarith

      simp at z_mem
      obtain ⟨g_max, f_g_max_eq⟩ := z_mem

      have f_const_fn := harmonic_abs_max_implies_const  f.toFun (by
        have f_harmonic := f.harmonic
        simp [Harmonic] at f_harmonic
        simp [Laplace_b, f_conv_mu]
        ext x
        simp
        have f_harmonic_real := f_harmonic x
        rw [sub_eq_zero]
        exact f_harmonic_real
      ) g_max (by
        intro a
        specialize z_max ((f.toFun a)) (by (
          simp
        ))
        rw [← f_g_max_eq] at z_max
        simpa using z_max
      )

      use (f g_max)
      ext a
      have app := congrFun f_const_fn a
      rw [app]
      simp [ConstLipschitzH]
      .
        rw [f_range_eq]
        apply Set.finite_range
      . apply Set.range_nonempty

    obtain ⟨f, nontrivial_f⟩ := exists_nontrivial_harmonic
    obtain ⟨z, f_eq_const⟩ := all_f_const f
    specialize nontrivial_f z
    contradiction


end GeneratesNS
end

theorem solution.{u_1} : type_of% @GeneratesNS.rho_g_case_finite_oai.{u_1} := @GeneratesNS.rho_g_case_finite_oai.{u_1}
