-- Prove2me | solution 1 for OAI.EuclideanFiveColor.proper_to_borel_weak
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T13:08:38.925641+00:00
-- url     : https://prove2.me/submissions/ea434ac0-3635-469a-beeb-dfc8b723feb5

import Mathlib
import Definitions.Def_EuclideanFiveColor
import Definitions.Def_OAIQ5T4002
import Theorems.Thm_OAI_PlaneFiveColor_Spectral_exists_terminal_factor
import Theorems.Thm_OAI_PlaneFiveColor_Spectral_radial_positive_near_zero

section
-- module Solutions.OAIQ5_T4.Compat
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Amenability
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

open scoped RealInnerProductSpace BoundedContinuousFunction
namespace EuclideanFiveColor.Amenable
variable (G : Type*) [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

variable {G}
namespace Mean
variable (M : Mean G)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma vector_shift (V : G →ᵇ H) (g : G) : M.vector (shift G g V) = M.vector V := by
  apply ext_inner_right ℝ; intro v
  rw [M.vector_pair, M.vector_pair]
  exact M.invariant g (pairing V v)

lemma vector_map {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [CompleteSpace J]
    (L : H →L[ℝ] J) (V : G →ᵇ H) :
    M.vector (L.compLeftContinuousBounded G V) = L (M.vector V) := by
  apply ext_inner_right ℝ; intro v
  rw [M.vector_pair, ← L.adjoint_inner_right, M.vector_pair]
  congr 1; ext x
  exact (L.adjoint_inner_right (V x) v).symm

end Mean
end EuclideanFiveColor.Amenable

namespace EuclideanFiveColor.Amenable.Mean

open scoped BoundedContinuousFunction
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable (M : Mean G)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma vector_orbit_invariant (U : G → H ≃ₗᵢ[ℝ] H)
    (hU : ∀ g h v, U (g+h) v = U g (U h v)) (v : H) (g : G) :
    U g (M.vector (orbit U v)) = M.vector (orbit U v) := by
  change (U g).toLinearIsometry.toContinuousLinearMap (M.vector (orbit U v)) = _
  rw [← M.vector_map (U g).toLinearIsometry.toContinuousLinearMap]
  have he : (U g).toLinearIsometry.toContinuousLinearMap.compLeftContinuousBounded G (orbit U v) =
      shift G g (orbit U v) := by
    ext h
    change U g (U h v) = U (h+g) v
    rw [add_comm h g, hU]
  rw [he, M.vector_shift]

end EuclideanFiveColor.Amenable.Mean

namespace EuclideanFiveColor.Amenable.Koopman
open MeasureTheory Filter
section Action
variable {G X E : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X] (μ : Measure X)
  [VAddInvariantMeasure G X μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma action_add (g h : G) (f : Lp E 2 μ) :
    action μ (g+h) f = action μ g (action μ h f) := linear_add μ g h f

lemma coe_action (g : G) (f : Lp E 2 μ) :
    action μ g f =ᵐ[μ] (fun x => f (g +ᵥ x)) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_vadd g μ)

end Action

end EuclideanFiveColor.Amenable.Koopman

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Basic
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.K_countable _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualPolishSpace _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.PlaneFiveColor.Spectral.rotErgodic _root_.OAI.PlaneFiveColor.Spectral.rotInvariant _root_.OAI.PlaneFiveColor.Spectral.rotMeasurable _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral

/-- The group-theoretic step behind the zero-mass coset argument. -/
theorem finite_image_trivial {G H : Type*} [Group G] [Group H] [Finite H]
    [RootableBy G ℕ] (f : G →* H) (g : G) : f g = 1 := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨x, hx⟩ := RootableBy.surjective_pow G ℕ (Fintype.card_ne_zero : Fintype.card H ≠ 0) g
  rw [← hx, map_pow, pow_card_eq_one]

theorem scalar_mem_C_iff {a : E} (ha : a ≠ 0) (d : D) : scalar a d ∈ C ↔ d ∈ C := by
  constructor
  · intro h
    have h' := scalar_mem_C a⁻¹ h
    simpa [ha] using h'
  · exact scalar_mem_C a

/-- Ordinary one-dimensional characters, proved from the covering property of exp. -/
theorem real_character (f : ℝ → Circle) (hf : Continuous f)
    (hmul : ∀ x y, f (x + y) = f x * f y) :
    ∃ a : ℝ, ∀ t, f t = Circle.exp (a * t) := by
  have hzero : f 0 = 1 := by
    have h := hmul 0 0
    exact (mul_left_cancel (show f 0 * 1 = f 0 * f 0 by simpa using h)).symm
  obtain ⟨F, ⟨hFzero, hFexp⟩, hFuniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      ⟨f, hf⟩ 0 0 (by simpa using hzero.symm)
  have hF (t : ℝ) : Circle.exp (F t) = f t := congrFun hFexp t
  have hadd (x y : ℝ) : F (x + y) = F x + F y := by
    let G : C(ℝ, ℝ) := ⟨fun t => F (t + y) - F y,
      (F.continuous.comp (continuous_id.add continuous_const)).sub continuous_const⟩
    have hG : G = F := hFuniq G ⟨by simp [G], by
      funext t
      change Circle.exp (F (t + y) - F y) = f t
      rw [Circle.exp_sub, hF, hF, hmul, mul_div_cancel_right]⟩
    have hh := congrArg (fun g : C(ℝ, ℝ) => g x) hG
    dsimp [G] at hh
    linarith
  let Fadd : ℝ →+ ℝ := { toFun := F, map_zero' := hFzero, map_add' := hadd }
  have hrat (q : ℚ) : F (q : ℝ) = (q : ℝ) * F 1 := by
    simpa [Fadd, Rat.smul_def] using map_rat_smul Fadd q (1 : ℝ)
  have hlinear : (fun t : ℝ => F t) = fun t => t * F 1 :=
    Rat.denseRange_cast.equalizer F.continuous
      (continuous_id.mul continuous_const) (funext hrat)
  refine ⟨F 1, fun t => ?_⟩
  rw [← hF, congrFun hlinear t, mul_comm]

theorem dense_F : Dense (F : Set ℝ) :=
  Dense.mono (Set.range_subset_iff.mpr fun q : ℚ =>
    mem_algebraicClosure_iff.mpr (isAlgebraic_ratCast ℚ q))
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ))

/-- The source's exact ordinary-character description on the dense real algebraic field. -/
theorem algebraic_real_character (f : F → Circle) (hf : Continuous f)
    (hmul : ∀ x y, f (x + y) = f x * f y) :
    ∃ a : ℝ, ∀ t : F, f t = Circle.exp (a * (t : ℝ)) := by
  have hzero : f 0 = 1 := by
    have h := hmul 0 0
    exact (mul_left_cancel (show f 0 * 1 = f 0 * f 0 by simpa using h)).symm
  let fHom : Multiplicative F →* Circle := {
    toFun := fun t => f t.toAdd
    map_one' := hzero
    map_mul' := fun _ _ => hmul _ _ }
  have hu : UniformContinuous f :=
    uniformContinuous_monoidHom_of_continuous (f := fHom) hf
  let g := dense_F.extend f
  have hg : Continuous g := (dense_F.uniformContinuous_extend hu).continuous
  have hext (t : F) : g (t : ℝ) = f t := dense_F.extend_eq hf t
  have hgmul : ∀ x y : ℝ, g (x + y) = g x * g y := by
    intro x y
    refine dense_F.denseRange_val.induction_on₂
      (p := fun x y => g (x + y) = g x * g y) ?_ ?_ x y
    · exact isClosed_eq (hg.comp (continuous_fst.add continuous_snd))
        ((hg.comp continuous_fst).mul (hg.comp continuous_snd))
    · intro x y
      change g ((x + y : F) : ℝ) = g (x : ℝ) * g (y : ℝ)
      simp only [hext, hmul]
  obtain ⟨a, ha⟩ := real_character g hg hgmul
  exact ⟨a, fun t => (hext t).symm.trans (ha t)⟩

theorem continuous_jF : Continuous jF := by
  apply ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro z
  exact Circle.exp.continuous.comp (continuous_id.mul continuous_const)

theorem measurableSet_CF : MeasurableSet CF := by
  change MeasurableSet (Set.range jF)
  rw [← Set.image_univ, ← Metric.iUnion_closedBall_nat (0 : ℝ), Set.image_iUnion]
  exact MeasurableSet.iUnion fun n =>
    ((isCompact_closedBall (0 : ℝ) (n : ℝ)).image continuous_jF).measurableSet

theorem continuous_restrictLine (a : E) : Continuous (restrictLine a) :=
  (lineHom a).continuous_comp_left

theorem mem_L_iff (a : E) (d : D) : d ∈ L a ↔ restrictLine a d ∈ CF := by
  constructor
  · intro hd
    obtain ⟨l, hl⟩ := algebraic_real_character
      (fun t : F => d (Multiplicative.ofAdd (a * ofF t))) hd (by
        intro t s
        rw [map_add, mul_add]
        exact map_mul d _ _)
    use l
    apply PontryaginDual.ext
    intro t
    exact (hl (Multiplicative.toAdd t)).symm
  · rintro ⟨l, hl⟩
    have h (t : F) : d (Multiplicative.ofAdd (a * ofF t)) = Circle.exp (l * (t : ℝ)) :=
      (congrArg (fun χ : DF => χ (Multiplicative.ofAdd t)) hl).symm
    change Continuous (fun t : F => d (Multiplicative.ofAdd (a * ofF t)))
    simp_rw [h]
    exact Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)

theorem measurableSet_L (a : E) : MeasurableSet (L a) := by
  have h : L a = restrictLine a ⁻¹' CF := by ext d; exact mem_L_iff a d
  rw [h]
  exact measurableSet_CF.preimage (continuous_restrictLine a).measurable

theorem reF_add_imF (z : E) : ofF (reF z) + imagUnit * ofF (imF z) = z := by
  apply Subtype.ext
  change ((z : ℂ).re : ℂ) + Complex.I * (z : ℂ).im = (z : ℂ)
  rw [mul_comm, Complex.re_add_im]

theorem line_add {a b : E} {d : D} (ha : d ∈ L a) (hb : d ∈ L b) :
    d ∈ L (a + b) := by
  have h (t : F) : d (Multiplicative.ofAdd ((a + b) * ofF t)) =
      d (Multiplicative.ofAdd (a * ofF t)) * d (Multiplicative.ofAdd (b * ofF t)) := by
    rw [add_mul]; exact map_mul d _ _
  change Continuous _
  simp_rw [h]
  exact ha.mul hb

theorem line_mul_real {a : E} {d : D} (ha : d ∈ L a) (t : F) :
    d ∈ L (a * ofF t) := by
  change Continuous _ at ha ⊢
  convert ha.comp (continuous_const.mul continuous_id : Continuous (fun s : F => t * s)) using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  simp only [Function.comp_apply, Pi.mul_apply, map_mul, mul_assoc]

theorem line_sub {a b : E} {d : D} (ha : d ∈ L a) (hb : d ∈ L b) :
    d ∈ L (a - b) := by
  have hn : d ∈ L (-b) := by simpa using line_mul_real hb (-1)
  simpa only [sub_eq_add_neg] using line_add ha hn

theorem orthogonal_lines {d : D} (h1 : d ∈ L 1) (hi : d ∈ L imagUnit) : d ∈ C := by
  obtain ⟨l, hl⟩ := (mem_L_iff 1 d).mp h1
  obtain ⟨e, he⟩ := (mem_L_iff imagUnit d).mp hi
  refine ⟨Multiplicative.ofAdd ((l : ℂ) + (e : ℂ) * Complex.I), ?_⟩
  apply PontryaginDual.ext
  intro z
  have hr (t : F) : d (Multiplicative.ofAdd (ofF t)) = Circle.exp (l * (t : ℝ)) := by
    have hh := congrArg (fun f : DF => f (Multiplicative.ofAdd t)) hl
    change Circle.exp (l * (t : ℝ)) = d (Multiplicative.ofAdd (1 * ofF t)) at hh
    simpa only [one_mul] using hh.symm
  have hi' (t : F) : d (Multiplicative.ofAdd (imagUnit * ofF t)) = Circle.exp (e * (t : ℝ)) :=
    (congrArg (fun f : DF => f (Multiplicative.ofAdd t)) he).symm
  change Circle.exp (inner ℝ ((l : ℂ) + (e : ℂ) * Complex.I) (embed z)) = d z
  have hd : d z = d (Multiplicative.ofAdd (ofF (reF (Multiplicative.toAdd z)))) *
      d (Multiplicative.ofAdd (imagUnit * ofF (imF (Multiplicative.toAdd z)))) := by
    calc
      d z = d (Multiplicative.ofAdd (ofF (reF (Multiplicative.toAdd z)) +
        imagUnit * ofF (imF (Multiplicative.toAdd z)))) :=
          congrArg d (congrArg Multiplicative.ofAdd (reF_add_imF (Multiplicative.toAdd z))).symm
      _ = _ := map_mul d _ _
  rw [hd, hr, hi', ← Circle.exp_add]
  congr 1
  simp [Complex.inner, embed, Complex.mul_re, Complex.mul_im, mul_comm]

/-- Two genuinely independent algebraic directions force an ordinary character. -/
theorem line_one_and_nonreal {d : D} (h1 : d ∈ L 1) {w : E}
    (hw : d ∈ L w) (hn : imF w ≠ 0) : d ∈ C := by
  have hr : d ∈ L (ofF (reF w)) := by simpa using line_mul_real h1 (reF w)
  have hsub := line_sub hw hr
  have him := line_mul_real hsub (imF w)⁻¹
  have heq : (w - ofF (reF w)) * ofF (imF w)⁻¹ = imagUnit := by
    have hz := reF_add_imF w
    have hzero : ofF (imF w) ≠ 0 := fun h => hn (ofF.injective (by simpa using h))
    rw [map_inv₀]
    calc
      (w - ofF (reF w)) * (ofF (imF w))⁻¹ =
        (imagUnit * ofF (imF w)) * (ofF (imF w))⁻¹ := by congr 1; linear_combination -hz
      _ = imagUnit := by rw [mul_assoc, mul_inv_cancel₀ hzero, mul_one]
  rw [heq] at him
  exact orthogonal_lines h1 him

theorem independent_lines {a b : E} (ha : a ≠ 0) (hn : imF (a⁻¹ * b) ≠ 0)
    {d : D} (hda : d ∈ L a) (hdb : d ∈ L b) : d ∈ C := by
  apply (scalar_mem_C_iff ha d).mp
  apply line_one_and_nonreal (w := a⁻¹ * b) (by simpa using hda) _ hn
  simpa [← mul_assoc, ha] using hdb

theorem real_rotation_square (u : K) (hi : imF (kCoeff u) = 0) : u ^ 2 = 1 := by
  have him : (u.val : ℂ).im = 0 := congrArg (fun x : F => (x : ℝ)) hi
  have hn : (u.val : ℂ).re * (u.val : ℂ).re = 1 := by
    have hh := Complex.sq_norm (u.val : ℂ)
    rw [Circle.norm_coe] at hh
    simpa [Complex.normSq_apply, him] using hh.symm
  apply Subtype.ext
  apply Subtype.ext
  change (u.val : ℂ) ^ 2 = 1
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im, him, hn]

/-- Squared rotations index the distinct unoriented algebraic lines. -/
theorem rotated_directions_independent {a : E} (ha : a ≠ 0) {u v : K}
    (huv : u ^ 2 ≠ v ^ 2) : imF ((a * kCoeff u)⁻¹ * (a * kCoeff v)) ≠ 0 := by
  intro h
  have heq : (a * kCoeff u)⁻¹ * (a * kCoeff v) = kCoeff (u⁻¹ * v) := by
    simp [mul_inv_rev, mul_assoc, ha]
  rw [heq] at h
  have hp := real_rotation_square (u⁻¹ * v) h
  apply huv
  have hp' : (u ^ 2)⁻¹ * (v ^ 2) = 1 := by simpa only [mul_pow, inv_pow] using hp
  exact inv_mul_eq_one.mp hp'

/-- Complete line-event conclusion of the source's null-events lemma. -/
theorem wild_line_null (ν : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0) : ν (L a) = 0 := by
  classical
  by_contra hn
  have hp : 0 < ν (L a) := pos_iff_ne_zero.mpr hn
  let root : K → K := fun u => Classical.choose (K_pow_surjective 2 (by norm_num) u)
  have hroot (u : K) : (root u) ^ 2 = u := Classical.choose_spec (K_pow_surjective 2 (by norm_num) u)
  let B (u : K) : Set D := L (a * kCoeff (root u)) \ (C : Set D)
  have hBm (u : K) : MeasurableSet (B u) := (measurableSet_L _).diff measurableSet_C
  have hpre (u : K) : (fun d : D => (root u) • d) ⁻¹' L a = L (a * kCoeff (root u)) := by
    ext d
    change scalar (kCoeff (root u)) d ∈ L a ↔ _
    rw [scalar_line, mul_comm]
  have hmass (u : K) : ν (B u) = ν (L a) := by
    change ν (L (a * kCoeff (root u)) \ (C : Set D)) = _
    rw [MeasureTheory.measure_sdiff_null hν.2, ← hpre]
    exact (hν.1 (root u)).measure_preimage (measurableSet_L a).nullMeasurableSet
  have hd : Pairwise (Function.onFun Disjoint B) := by
    intro u v huv
    change Disjoint (B u) (B v)
    rw [Set.disjoint_left]
    rintro d ⟨hdu, hdc⟩ ⟨hdv, _⟩
    apply hdc
    apply independent_lines (mul_ne_zero ha (kCoeff_ne_zero _))
      (rotated_directions_independent ha _) hdu hdv
    simpa only [hroot] using huv
  have hf := MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion ν hp (As := B)
    hBm hd (MeasureTheory.measure_ne_top ν _)
  have hu : {u : K | ν (L a) ≤ ν (B u)} = Set.univ := by ext u; simp [hmass]
  rw [hu] at hf
  let := Set.finite_univ_iff.mp hf
  have hm := finite_image_trivial (MonoidHom.id K) minusOne
  have hb := congrArg (fun u : K => (u.val : ℂ)) hm
  norm_num [minusOne] at hb

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_RelativeCenters
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

open MeasureTheory
open scoped ENNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.KernelSupport

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

lemma compProd_map_base (ν : Measure Y) [SFinite ν] (κ : Kernel Y Z)
    [IsSFiniteKernel κ] (R : Y ≃ᵐ Y) :
    (ν.map R) ⊗ₘ (κ.comap R.symm R.symm.measurable) =
      (ν ⊗ₘ κ).map (Prod.map R id) := by
  ext s hs
  rw [Measure.compProd_apply hs,
    Measure.map_apply (R.measurable.prodMap measurable_id) hs,
    Measure.compProd_apply ((R.measurable.prodMap measurable_id) hs),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) R.measurable]
  apply lintegral_congr
  intro y
  simp only [Kernel.comap_apply, R.symm_apply_apply]
  rfl

lemma condDistrib_comp_equiv [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Z) (p : X → Y) (hf : Measurable f) (hp : Measurable p)
    (R : Y ≃ᵐ Y) :
    condDistrib f (R ∘ p) μ =ᵐ[μ.map (R ∘ p)]
      (condDistrib f p μ).comap R.symm R.symm.measurable := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (R.measurable.comp hp) hf
  rw [← Measure.map_map R.measurable hp, compProd_map_base,
    compProd_map_condDistrib hf.aemeasurable,
    Measure.map_map (R.measurable.prodMap measurable_id) (hp.prodMk hf)]
  rfl

/-- Changing both coordinates of a conditional law by invertible measurable
maps commutes with conditional sampling. -/
lemma condDistrib_equivariant [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Z) (p : X → Y) (hf : Measurable f) (hp : Measurable p)
    (S : X ≃ᵐ X) (R : Y ≃ᵐ Y) (T : Z → Z) (hT : Measurable T)
    (hS : MeasurePreserving S μ μ)
    (hRp : p ∘ S =ᵐ[μ] R ∘ p) (hTf : f ∘ S =ᵐ[μ] T ∘ f) :
    ∀ᵐ y ∂μ.map p, condDistrib f p μ (R y) = (condDistrib f p μ y).map T := by
  have hR : (μ.map p).map R = μ.map p := by
    rw [Measure.map_map R.measurable hp, ← Measure.map_congr hRp,
      ← Measure.map_map hp S.measurable, hS.map_eq]
  have hRS : μ.map (p ∘ S) = μ.map p := by
    rw [← Measure.map_map hp S.measurable, hS.map_eq]
  have hm := condDistrib_map (X := p) (Y := f) (ν := μ) (f := S)
    (hp.aemeasurable) (hf.aemeasurable) S.measurable.aemeasurable
  simp only [hS.map_eq, hRS] at hm
  rw [condDistrib_congr hTf hRp] at hm
  have hc := condDistrib_comp_equiv μ (T ∘ f) p (hT.comp hf) hp R
  have hh : μ.map (R ∘ p) = μ.map p := by
    rw [← Measure.map_map R.measurable hp, hR]
  rw [hh] at hc
  have he := condDistrib_comp (μ := μ) (mβ := inferInstance) p hf.aemeasurable hT
  have hcomp : ∀ᵐ y ∂μ.map p,
      condDistrib f p μ y = (condDistrib f p μ (R.symm y)).map T := by
    have he' : ∀ᵐ y ∂μ.map p,
        condDistrib (T ∘ f) p μ (R.symm y) =
          (condDistrib f p μ (R.symm y)).map T := by
      have hRinv : MeasurePreserving R.symm (μ.map p) (μ.map p) := by
        refine ⟨R.symm.measurable, ?_⟩
        calc
          (μ.map p).map R.symm = ((μ.map p).map R).map R.symm := by rw [hR]
          _ = μ.map p := R.map_symm_map
      exact hRinv.quasiMeasurePreserving.ae <| he.mono fun y hy => by
        simpa only [Kernel.map_apply _ hT] using hy
    filter_upwards [hm, hc, he'] with y h₁ h₂ h₃
    simpa only [Kernel.comap_apply] using h₁.trans (h₂.trans h₃)
  have hRpres : MeasurePreserving R (μ.map p) (μ.map p) := ⟨R.measurable, hR⟩
  have hfinal := hRpres.quasiMeasurePreserving.ae hcomp
  filter_upwards [hfinal] with y hy
  simpa only [R.symm_apply_apply] using hy

end EuclideanFiveColor.KernelSupport

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_ConditionalSelection
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators

open MeasureTheory
open scoped BigOperators

open MeasureTheory

open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.ConditionalFiber
variable {X W G V : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace W] [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G]

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma comp_identity_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) :
    (condDistrib id p μ) ∘ₘ μ.map p = μ := by
  simpa using condDistrib_comp_map hp.aemeasurable (measurable_id.aemeasurable (μ := μ))

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma ae_fiber_of_ae (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ w ∂μ.map p, ∀ᵐ x ∂condDistrib id p μ w, P x := by
  exact Measure.ae_ae_of_ae_comp (by rwa [comp_identity_fiber μ p hp])

lemma map_identity_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : AEMeasurable p μ) (b : X → G) (hb : Measurable b) :
    ∀ᵐ w ∂μ.map p, (condDistrib id p μ w).map b = condDistrib b p μ w := by
  filter_upwards [condDistrib_comp p
    (measurable_id.aemeasurable (μ := μ)) hb] with w hw
  simpa [Kernel.map_apply _ hb] using hw.symm

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma ae_in_own_fiber [StandardBorelSpace W] [Nonempty W]
    (μ : Measure X) [IsFiniteMeasure μ] (p : X → W) (hp : Measurable p) :
    ∀ᵐ w ∂μ.map p, ∀ᵐ x ∂condDistrib id p μ w, p x = w := by
  filter_upwards [map_identity_fiber μ p hp.aemeasurable p hp,
    condDistrib_self p] with w hw hs
  have he : (condDistrib id p μ w).map p = Measure.dirac w := by
    rw [hw, hs]; rfl
  apply ae_of_ae_map (p := fun z : W => z = w) hp.aemeasurable
  rw [he]
  simp

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma integral_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) (f : X → V) (hf : Integrable f μ) :
    ∫ w, (∫ x, f x ∂condDistrib id p μ w) ∂μ.map p = ∫ x, f x ∂μ := by
  have hi : Integrable f ((condDistrib id p μ) ∘ₘ μ.map p) := by
    rwa [comp_identity_fiber μ p hp]
  rw [Measure.comp_eq_comp_const_apply] at hi
  have he := Kernel.integral_comp hi
  simpa [Kernel.const_apply, ← Measure.comp_eq_comp_const_apply,
    comp_identity_fiber μ p hp] using he.symm

end EuclideanFiveColor.ConditionalFiber

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Characters
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualPolishSpace _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate

noncomputable section
open scoped BigOperators
namespace PlaneFiveColor.ContinuousCharacters

theorem abs_arg_exp_le (t : ℝ) : |Complex.arg (Circle.exp t : ℂ)| ≤ |t| := by
  by_cases h : |t| ≤ Real.pi
  · rcases (abs_le.mp h) with ⟨hl, hr⟩
    rcases eq_or_lt_of_le hl with hh | hh
    · have ht : t = -Real.pi := hh.symm
      rw [ht, Circle.coe_exp]
      simp [Complex.arg_neg_one]
    · rw [Circle.arg_exp hh hr]
  · have ha : |Complex.arg (Circle.exp t : ℂ)| ≤ Real.pi :=
      abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
    exact ha.trans (le_of_not_ge h)

theorem abs_arg_pow_le (z : Circle) (n : ℕ) :
    |Complex.arg (z ^ n : Circle)| ≤ n * |Complex.arg (z : ℂ)| := by
  have he : Circle.exp ((n : ℝ) * Complex.arg (z : ℂ)) = z ^ n := by
    rw [Circle.exp_natCast_mul, Circle.exp_arg]
  rw [← he]
  simpa [abs_mul] using abs_arg_exp_le ((n : ℝ) * Complex.arg (z : ℂ))

theorem frequency_abs_mono (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1) ^ 2) :
    Monotone (fun n => |frequency X n|) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [frequency, abs_mul, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
  rw [hX n]
  calc
    2 ^ n * |Complex.arg (X (n+1) ^ 2 : Circle)| ≤
        2 ^ n * (2 * |Complex.arg (X (n+1) : ℂ)|) := by
      gcongr
      simpa using abs_arg_pow_le (X (n+1)) 2
    _ = _ := by ring

theorem frequency_exp_previous (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1)^2)
    (n : ℕ) : Circle.exp (frequency X (n+1) / (2 : ℝ)^n) = X n := by
  rw [hX n, ← exp_frequency_div X (n+1), ← Circle.exp_natCast_mul]
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

theorem frequency_stabilizes (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1)^2)
    (R : ℝ) (hR : ∀ n, |frequency X n| ≤ R) :
    ∃ N, ∀ n, N ≤ n → frequency X n = frequency X N := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((Filter.tendsto_atTop.1
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)))
    (R / Real.pi + 1))
  have hp (n : ℕ) (hn : N ≤ n) : R < Real.pi * (2 : ℝ)^n := by
    have ht := hN n hn
    have hπ := Real.pi_pos
    have heq : R / Real.pi * Real.pi = R := div_mul_cancel₀ _ Real.pi_ne_zero
    nlinarith
  have hstep (n : ℕ) (hn : N ≤ n) : frequency X (n+1) = frequency X n := by
    have hb (m : ℕ) : |frequency X m / (2 : ℝ)^n| < Real.pi := by
      rw [abs_div, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
      exact (div_lt_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
        ((hR m).trans_lt (hp n hn))
    have he : frequency X (n+1) / (2 : ℝ)^n = frequency X n / (2 : ℝ)^n := by
      apply Circle.exp_injOn_Ico (a := -Real.pi) (b := Real.pi) (by linarith)
      · exact ⟨(abs_lt.mp (hb (n+1))).1.le, (abs_lt.mp (hb (n+1))).2⟩
      · exact ⟨(abs_lt.mp (hb n)).1.le, (abs_lt.mp (hb n)).2⟩
      · rw [frequency_exp_previous X hX, exp_frequency_div]
    exact (div_left_inj' (pow_ne_zero _ (by norm_num))).mp he
  refine ⟨N, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => exact (hstep n hn).trans ih

/-- The quantitative lower chord bound on the principal argument. -/
theorem chord_bound (z : Circle) :
    2 / Real.pi * |Complex.arg (z : ℂ)| ≤ ‖(z : ℂ) - 1‖ := by
  have ha : |Complex.arg (z : ℂ)| ≤ Real.pi :=
    abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have hc := Real.cos_le_one_sub_mul_cos_sq ha
  have hr := Complex.norm_mul_cos_arg (z : ℂ)
  have hn := Complex.normSq_sub (z : ℂ) 1
  simp only [Circle.norm_coe, one_mul] at hr
  simp only [Complex.normSq_eq_norm_sq, Circle.norm_coe, map_one,
    mul_one, one_pow] at hn
  have hp := Real.pi_pos
  have hπ : (0 : ℝ) < Real.pi ^ 2 := sq_pos_of_pos hp
  have h0 : 0 ≤ 2 / Real.pi * |Complex.arg (z : ℂ)| := by positivity
  have hsq : (2 / Real.pi * |Complex.arg (z : ℂ)|)^2 ≤ ‖(z : ℂ)-1‖^2 := by
    rw [mul_pow, sq_abs, div_pow]
    rw [hr] at hc
    calc
      2 ^ 2 / Real.pi ^ 2 * (Complex.arg (z : ℂ))^2 =
          2 * (2 / Real.pi ^ 2 * (Complex.arg (z : ℂ))^2) := by ring
      _ ≤ 2 * (1 - (z : ℂ).re) := by linarith
      _ = _ := by linarith
  exact (sq_le_sq₀ h0 (norm_nonneg _)).mp hsq

/-- Cesàro averages of a circle point are small away from one. -/
theorem geom_sum_chord_bound (z : Circle) (m : ℕ) :
    ‖∑ k ∈ Finset.range m, (z : ℂ)^k‖ * ‖(z : ℂ)-1‖ ≤ 2 := by
  rw [← norm_mul, geom_sum_mul]
  calc
    ‖(z : ℂ)^m-1‖ ≤ ‖(z : ℂ)^m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by simp only [norm_pow, Circle.norm_coe, norm_one, one_pow]; norm_num

/-- A large canonical frequency has a large averaged real deviation. -/
theorem average_deviation (z : Circle) (m : ℕ)
    (h : 4 ≤ (m : ℝ) * ‖(z : ℂ)-1‖) :
    (m : ℝ) / 2 ≤ ∑ k ∈ Finset.range m, (1 - ((z : ℂ)^k).re) := by
  have hn : 0 < ‖(z : ℂ)-1‖ := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    by_contra hh
    have hz := le_antisymm (le_of_not_gt hh) (norm_nonneg ((z : ℂ)-1))
    rw [hz, mul_zero] at h
    norm_num at h
  have hb := geom_sum_chord_bound z m
  have hr := (Complex.re_le_norm (∑ k ∈ Finset.range m, (z : ℂ)^k))
  have hs : (∑ k ∈ Finset.range m, (z : ℂ)^k).re ≤ (m : ℝ)/2 := by
    nlinarith [norm_nonneg (∑ k ∈ Finset.range m, (z : ℂ)^k)]
  simp only [Complex.re_sum] at hs
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  linarith

open MeasureTheory

lemma deviation_bound (z : Circle) (k : ℕ) : 0 ≤ deviation z k ∧ deviation z k ≤ 2 := by
  have h := Complex.abs_re_le_norm ((z : ℂ)^k)
  simp only [norm_pow, Circle.norm_coe, one_pow] at h
  have hh := abs_le.mp h
  constructor <;> dsimp [deviation] <;> linarith

lemma deviation_measurable {Ω : Type*} [MeasurableSpace Ω] (X : Ω → Circle)
    (hX : Measurable (fun x => (X x : ℂ))) (k : ℕ) : Measurable (fun x => deviation (X x) k) := by
  exact measurable_const.sub (Complex.measurable_re.comp (hX.pow_const k))

lemma deviation_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : Ω → Circle) (hX : Measurable (fun x => (X x : ℂ))) (k : ℕ) :
    Integrable (fun x => deviation (X x) k) μ := by
  apply Integrable.of_bound (deviation_measurable X hX k).aestronglyMeasurable 2
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (deviation_bound (X x) k).1] using
    (deviation_bound (X x) k).2

/-- Uniform small deviations imply a quantitative frequency-tail bound. -/
theorem frequency_tail_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : Ω → Circle) (hX : Measurable (fun x => (X x : ℂ)))
    (n m : ℕ) (hm : 0 < m) (R ε : ℝ)
    (hR : 4 ≤ (m : ℝ) * (2 / Real.pi) * (R / (2 : ℝ)^n))
    (hε : ∀ k ∈ Finset.range m, ∫ x, deviation (X x) k ∂μ ≤ ε) :
    μ.real {x | R ≤ |(2 : ℝ)^n * Complex.arg (X x : ℂ)|} ≤ 2 * ε := by
  let S : Ω → ℝ := fun x => ∑ k ∈ Finset.range m, deviation (X x) k
  have hS : Integrable S μ := by
    apply integrable_finsetSum
    intro k hk
    exact deviation_integrable μ X hX k
  have hSn : 0 ≤ᵐ[μ] S := Filter.Eventually.of_forall fun x =>
    Finset.sum_nonneg fun k hk => (deviation_bound (X x) k).1
  have hi : ∫ x, S x ∂μ ≤ (m : ℝ)*ε := by
    dsimp [S]
    rw [integral_finsetSum _ (fun k _ => deviation_integrable μ X hX k)]
    calc
      _ ≤ ∑ _k ∈ Finset.range m, ε := Finset.sum_le_sum hε
      _ = _ := by simp
  have ht : {x | R ≤ |(2 : ℝ)^n * Complex.arg (X x : ℂ)|} ⊆
      {x | (m : ℝ)/2 ≤ S x} := by
    intro x hx
    apply average_deviation (X x) m
    have hn : 0 < (2 : ℝ)^n := pow_pos (by norm_num) _
    have hf : R / (2 : ℝ)^n ≤ |Complex.arg (X x : ℂ)| := by
      apply (div_le_iff₀ hn).mpr
      simpa only [Set.mem_ofPred_eq, abs_mul, abs_of_pos hn, mul_comm] using hx
    calc
      4 ≤ (m : ℝ) * (2 / Real.pi) * (R / (2 : ℝ)^n) := hR
      _ ≤ (m : ℝ) * (2 / Real.pi) * |Complex.arg (X x : ℂ)| := by gcongr
      _ = (m : ℝ) * (2 / Real.pi * |Complex.arg (X x : ℂ)|) := by ring
      _ ≤ _ := by gcongr; exact chord_bound (X x)
  have hmark := mul_meas_ge_le_integral_of_nonneg hSn hS ((m : ℝ)/2)
  have hmono := measureReal_mono (μ := μ) ht
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  nlinarith

/-- Choosing a Cesàro window within a fixed neighborhood of zero gives
frequency tightness with a bound independent of the dyadic level. -/
theorem dyadic_tail_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → Circle) (hX : ∀ n, Measurable (fun x => (X n x : ℂ)))
    (δ ε : ℝ) (hδ : 0 < δ)
    (he : ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ →
      ∫ x, deviation (X n x) k ∂μ ≤ ε) (n : ℕ) :
    μ.real {x | 2 * Real.pi / δ ≤ |frequency (fun j => X j x) n|} ≤ 2*ε := by
  let m := Nat.ceil (δ * (2 : ℝ)^n)
  have hn : 0 < (2 : ℝ)^n := pow_pos (by norm_num) _
  have hm : 0 < m := Nat.ceil_pos.mpr (mul_pos hδ hn)
  apply frequency_tail_bound μ (X n) (hX n) n m hm
  · calc
      4 = (δ * (2 : ℝ)^n) * (2 / Real.pi) * ((2 * Real.pi / δ)/(2 : ℝ)^n) := by
        field_simp
        ring
      _ ≤ _ := by
        gcongr
        exact Nat.le_ceil _
  · intro k hk
    apply he
    apply (div_lt_iff₀ hn).mpr
    simpa only [mul_comm] using Nat.lt_ceil.mp (Finset.mem_range.mp hk)

/-- A measure with coefficients continuous at zero is almost surely supported
on dyadic paths whose principal frequencies are bounded. -/
theorem dyadic_frequencies_ae_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → Circle) (hX : ∀ n, Measurable (fun x => (X n x : ℂ)))
    (hcoh : ∀ x n, X n x = X (n+1) x ^ 2)
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ → ∫ x, deviation (X n x) k ∂μ ≤ ε) :
    ∀ᵐ x ∂μ, ∃ R : ℝ, ∀ n, |frequency (fun j => X j x) n| ≤ R := by
  rw [ae_iff]
  apply (measureReal_eq_zero_iff (μ := μ)).mp
  apply le_antisymm _ measureReal_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ, hδ, he⟩ := hcont (ε/2) (by positivity)
  let R := 2 * Real.pi / δ
  let A : ℕ → Set Ω := fun n => {x | R ≤ |frequency (fun j => X j x) n|}
  have hmono : Monotone A := by
    intro n m hnm x hx
    exact hx.trans (frequency_abs_mono _ (hcoh x) hnm)
  have hA (n : ℕ) : μ (A n) ≤ ENNReal.ofReal ε := by
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hε.le).mpr
    have ht := dyadic_tail_bound μ X hX δ (ε/2) hδ he n
    dsimp [A, R]
    simpa only [measureReal_def, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using ht
  have hi : μ (⋃ n, A n) ≤ ENNReal.ofReal ε := by
    rw [hmono.measure_iUnion]
    exact iSup_le hA
  have hsub : {x | ¬ ∃ R : ℝ, ∀ n, |frequency (fun j => X j x) n| ≤ R} ⊆
      ⋃ n, A n := by
    intro x hx
    push Not at hx
    obtain ⟨n, hn⟩ := hx R
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
  have hz := ENNReal.toReal_le_of_le_ofReal hε.le ((measure_mono hsub).trans hi)
  simpa only [zero_add, measureReal_def] using hz

/-- The canonical frequencies of almost every such path eventually stabilize. -/
theorem dyadic_frequencies_ae_stable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → Circle) (hX : ∀ n, Measurable (fun x => (X n x : ℂ)))
    (hcoh : ∀ x n, X n x = X (n+1) x ^ 2)
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ → ∫ x, deviation (X n x) k ∂μ ≤ ε) :
    ∀ᵐ x ∂μ, ∃ N, ∀ n, N ≤ n →
      frequency (fun j => X j x) n = frequency (fun j => X j x) N := by
  filter_upwards [dyadic_frequencies_ae_bounded μ X hX hcoh hcont] with x hx
  obtain ⟨R, hR⟩ := hx
  exact frequency_stabilizes _ (hcoh x) R hR

/-- A stable coherent path is an ordinary frequency on every dyadic scale. -/
theorem ordinary_of_stable (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1)^2)
    (N : ℕ) (hN : ∀ n, N ≤ n → frequency X n = frequency X N) :
    ∀ n, X n = Circle.exp (frequency X N / (2 : ℝ)^n) := by
  intro n
  refine Nat.decreasingInduction (n := max N n)
    (motive := fun k _ => X k = Circle.exp (frequency X N / (2 : ℝ)^k))
    ?_ ?_ (Nat.le_max_right N n)
  · intro k hk ih
    rw [hX k, ih, ← Circle.exp_natCast_mul]
    congr 1
    push_cast
    rw [pow_succ]
    field_simp
  · rw [← exp_frequency_div X (max N n), hN _ (Nat.le_max_left N n)]

lemma dyadicApprox_error (t : F) (n : ℕ) :
    |(dyadicApprox t n : ℝ) - (t : ℝ)| ≤ ((2 : ℝ)^n)⁻¹ := by
  have hpos : 0 < (2 : ℝ)^n := pow_pos (by norm_num) _
  have hl := Int.floor_le ((2 : ℝ)^n * (t : ℝ))
  have hr := Int.lt_floor_add_one ((2 : ℝ)^n * (t : ℝ))
  change |(Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ)/(2 : ℝ)^n - (t : ℝ)| ≤ _
  calc
    _ = |(Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ) - (2 : ℝ)^n * (t : ℝ)| /
        (2 : ℝ)^n := by
      have heq : (Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ)/(2 : ℝ)^n - (t : ℝ) =
          ((Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ) - (2 : ℝ)^n * (t : ℝ))/(2 : ℝ)^n := by
        field_simp
      rw [heq, abs_div, abs_of_pos hpos]
    _ ≤ 1 / (2 : ℝ)^n := by
      gcongr
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    _ = _ := one_div _

lemma dyadicApprox_tendsto (t : F) :
    Filter.Tendsto (fun n => (dyadicApprox t n : ℝ)) Filter.atTop (nhds (t : ℝ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => dyadicApprox_error t n)
  exact tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

/-- Exact squared distance identity for unit characters. -/
lemma circle_sq_dist (z w : Circle) :
    ‖(z : ℂ)-(w : ℂ)‖^2 = 2 * deviation (z/w) 1 := by
  have h := Complex.normSq_sub (z : ℂ) (w : ℂ)
  simp only [Complex.normSq_eq_norm_sq, Circle.norm_coe, one_pow] at h
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, ← div_eq_mul_inv] at h
  simp only [Circle.coe_div] at h
  dsimp [deviation]
  rw [pow_one]
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

lemma coeff_small (μ : Measure Ω) (χ : Ω → Multiplicative F →* Circle)
    (hc : ContinuousAt (coeff μ χ) 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : F, |(t : ℝ)| < δ → coeff μ χ t ≤ ε := by
  obtain ⟨δ, hδ, hh⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hdist : dist t 0 < δ := by
    rw [dist_eq_norm, sub_zero]
    change ‖(t : ℝ)‖ < δ
    exact ht
  have hb := hh hdist
  rw [coeff_zero, dist_zero_right, Real.norm_eq_abs] at hb
  exact (le_abs_self _).trans hb.le

lemma char_nat_dyadic (χ : Multiplicative F →* Circle) (n k : ℕ) :
    χ (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) ^ k =
      χ (Multiplicative.ofAdd ((k : F)/(2 : F)^n)) := by
  rw [← map_pow]
  congr 1
  change Multiplicative.ofAdd ((k : ℕ) • ((2 : F)^n)⁻¹) = _
  simp only [nsmul_eq_mul, div_eq_mul_inv]

lemma char_int_dyadic (χ : Multiplicative F →* Circle) (k : ℤ) (m : ℕ) :
    χ (Multiplicative.ofAdd (((2 : F)^m)⁻¹)) ^ k =
      χ (Multiplicative.ofAdd ((k : F)/(2 : F)^m)) := by
  rw [← map_zpow]
  congr 1
  change Multiplicative.ofAdd ((k : ℤ) • ((2 : F)^m)⁻¹) = _
  simp only [zsmul_eq_mul, div_eq_mul_inv]

lemma char_dyadic_coherent (χ : Multiplicative F →* Circle) (n : ℕ) :
    χ (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) =
      χ (Multiplicative.ofAdd (((2 : F)^(n+1))⁻¹)) ^ 2 := by
  rw [char_nat_dyadic]
  congr 2
  norm_num only [Nat.cast_ofNat]
  rw [pow_succ]
  field_simp

/-- Continuous averaged coefficients give ordinary frequencies on dyadics a.e. -/
theorem character_ae_dyadic (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)))
    (hc : ContinuousAt (coeff μ χ) 0) :
    ∀ᵐ x ∂μ, ∃ l : ℝ, ∀ n : ℕ,
      χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) = Circle.exp (l/(2 : ℝ)^n) := by
  let X : ℕ → Ω → Circle := fun n x => χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹))
  have hX : ∀ n, Measurable (fun x => (X n x : ℂ)) := fun n => hχ _
  have hcoh : ∀ x n, X n x = X (n+1) x ^ 2 := fun x n => char_dyadic_coherent _ _
  have hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ → ∫ x, deviation (X n x) k ∂μ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hh⟩ := coeff_small μ χ hc ε hε
    refine ⟨δ, hδ, fun n k hk => ?_⟩
    have he : (∫ x, deviation (X n x) k ∂μ) = coeff μ χ ((k : F)/(2 : F)^n) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [coeff, deviation, X]
      rw [← Circle.coe_pow, char_nat_dyadic, pow_one]
    rw [he]
    apply hh
    change |(k : ℝ)/(2 : ℝ)^n| < δ
    simpa only [abs_of_nonneg
      (div_nonneg (Nat.cast_nonneg k) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))] using hk
  filter_upwards [dyadic_frequencies_ae_stable μ X hX hcoh hcont] with x hx
  obtain ⟨N, hN⟩ := hx
  exact ⟨frequency (fun n => X n x) N, ordinary_of_stable _ (hcoh x) N hN⟩

lemma char_sub (χ : Multiplicative F →* Circle) (t s : F) :
    χ (Multiplicative.ofAdd (t-s)) =
      χ (Multiplicative.ofAdd t) / χ (Multiplicative.ofAdd s) := by
  exact map_div χ (Multiplicative.ofAdd t) (Multiplicative.ofAdd s)

lemma char_sq_distance (χ : Multiplicative F →* Circle) (t s : F) :
    ‖(χ (Multiplicative.ofAdd t) : ℂ)-(χ (Multiplicative.ofAdd s) : ℂ)‖^2 =
      2 * deviation (χ (Multiplicative.ofAdd (t-s))) 1 := by
  rw [circle_sq_dist, char_sub]

lemma char_sq_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ))) (t s : F) :
    Integrable (fun x => ‖(χ x (Multiplicative.ofAdd t) : ℂ)-
      (χ x (Multiplicative.ofAdd s) : ℂ)‖^2) μ := by
  simp_rw [char_sq_distance]
  exact (deviation_integrable μ _ (hχ (t-s)) 1).const_mul 2

lemma char_sq_integral (μ : Measure Ω) (χ : Ω → Multiplicative F →* Circle) (t s : F) :
    (∫ x, ‖(χ x (Multiplicative.ofAdd t) : ℂ)-
      (χ x (Multiplicative.ofAdd s) : ℂ)‖^2 ∂μ) = 2 * coeff μ χ (t-s) := by
  simp_rw [char_sq_distance]
  exact integral_const_mul _ _

/-- At coefficient-continuity points, dyadic character evaluations converge in measure. -/
lemma character_tendstoInMeasure (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)))
    (hc : ContinuousAt (coeff μ χ) 0) (r : ℕ → F) (t : F)
    (hr : Filter.Tendsto r Filter.atTop (nhds t)) :
    TendstoInMeasure μ (fun n x => (χ x (Multiplicative.ofAdd (r n)) : ℂ))
      Filter.atTop (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have hpos : 0 < ε^2 := sq_pos_of_pos hε
  have hdiff : Filter.Tendsto (fun n => r n - t) Filter.atTop (nhds 0) := by
    simpa only [sub_self] using hr.sub (tendsto_const_nhds (x := t))
  have hint : Filter.Tendsto (fun n => (∫ x, ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-
      (χ x (Multiplicative.ofAdd t) : ℂ)‖^2 ∂μ)/ε^2) Filter.atTop (nhds 0) := by
    simp_rw [char_sq_integral]
    simpa only [Function.comp_def, coeff_zero, mul_zero, zero_div] using
      ((hc.tendsto.comp hdiff).const_mul 2).div_const (ε^2)
  apply squeeze_zero (fun n => measureReal_nonneg) _ hint
  intro n
  apply (le_div_iff₀ hpos).mpr
  have hh := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg
      ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-(χ x (Multiplicative.ofAdd t) : ℂ)‖)
    (char_sq_integrable μ χ hχ (r n) t) (ε^2)
  have heq : {x | ε^2 ≤ ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-
    (χ x (Multiplicative.ofAdd t) : ℂ)‖^2} =
      {x | ε ≤ ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-
    (χ x (Multiplicative.ofAdd t) : ℂ)‖} := by
    ext x
    exact sq_le_sq₀ hε.le (norm_nonneg _)
  rw [heq] at hh
  simpa only [mul_comm] using hh

lemma char_dyadicApprox_eq (χ : Multiplicative F →* Circle) (l : ℝ)
    (hl : ∀ n : ℕ, χ (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) =
      Circle.exp (l/(2 : ℝ)^n)) (t : F) (n : ℕ) :
    χ (Multiplicative.ofAdd (dyadicApprox t n)) = Circle.exp (l * (dyadicApprox t n : ℝ)) := by
  rw [dyadicApprox, ← char_int_dyadic, hl, ← Circle.exp_intCast_mul]
  congr 1
  change (Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ) * (l/(2 : ℝ)^n) =
    l * ((Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ)/(2 : ℝ)^n)
  ring

/-- Direct ordinary-character support theorem on the algebraic real line.
No Bochner representing-measure theorem is an input: frequency tightness and
an a.e. subsequence argument prove the actual simultaneous character formula. -/
theorem character_ae_ordinary (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)))
    (hc : ContinuousAt (coeff μ χ) 0) :
    ∀ᵐ x ∂μ, ∃ l : ℝ, ∀ t : F,
      χ x (Multiplicative.ofAdd t) = Circle.exp (l*(t : ℝ)) := by
  have ha (t : F) : ∀ᵐ x ∂μ, ∀ l : ℝ,
      (∀ n : ℕ, χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) = Circle.exp (l/(2 : ℝ)^n)) →
      χ x (Multiplicative.ofAdd t) = Circle.exp (l*(t : ℝ)) := by
    have hr : Filter.Tendsto (dyadicApprox t) Filter.atTop (nhds t) :=
      tendsto_subtype_rng.mpr (dyadicApprox_tendsto t)
    obtain ⟨ns, hns, hae⟩ :=
      (character_tendstoInMeasure μ χ hχ hc (dyadicApprox t) t hr).exists_seq_tendsto_ae
    filter_upwards [hae] with x hx
    intro l hl
    have hlim : Filter.Tendsto
        (fun n => (Circle.exp (l*(dyadicApprox t (ns n) : ℝ)) : ℂ)) Filter.atTop
        (nhds (Circle.exp (l*(t : ℝ)) : ℂ)) := by
      apply (continuous_subtype_val.comp Circle.exp.continuous).continuousAt.tendsto.comp
      exact tendsto_const_nhds.mul ((dyadicApprox_tendsto t).comp hns.tendsto_atTop)
    have heq : (fun n => (χ x (Multiplicative.ofAdd (dyadicApprox t (ns n))) : ℂ)) =
        fun n => (Circle.exp (l*(dyadicApprox t (ns n) : ℝ)) : ℂ) := by
      funext n
      rw [char_dyadicApprox_eq _ l hl]
    rw [heq] at hx
    exact Subtype.ext (tendsto_nhds_unique hx hlim)
  have hall : ∀ᵐ x ∂μ, ∀ t : F, ∀ l : ℝ,
      (∀ n : ℕ, χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) = Circle.exp (l/(2 : ℝ)^n)) →
      χ x (Multiplicative.ofAdd t) = Circle.exp (l*(t : ℝ)) := ae_all_iff.mpr ha
  filter_upwards [character_ae_dyadic μ χ hχ hc, hall] with x hx hxall
  obtain ⟨l, hl⟩ := hx
  exact ⟨l, fun t => hxall t l hl⟩

end PlaneFiveColor.ContinuousCharacters

namespace PlaneFiveColor.Spectral
open MeasureTheory

/-- The exact replacement of Bochner's support step for an arbitrary finite
weight absolutely continuous with respect to a wild law. -/
theorem wild_continuous_coefficient_zero (ν μ : Measure D) [IsProbabilityMeasure ν]
    [IsFiniteMeasure μ] (hν : IsWild ν) (hμ : μ ≪ ν) {a : E} (ha : a ≠ 0)
    (hc : ContinuousAt (ContinuousCharacters.coeff μ (lineCharacter a)) 0) : μ = 0 := by
  have hs := ContinuousCharacters.character_ae_ordinary μ (lineCharacter a)
    (lineCharacter_measurable a) hc
  have hL : ∀ᵐ d ∂μ, d ∈ L a := by
    filter_upwards [hs] with d hd
    obtain ⟨l, hl⟩ := hd
    apply (mem_L_iff a d).mpr
    refine ⟨l, ?_⟩
    apply PontryaginDual.ext
    intro t
    exact (hl (Multiplicative.toAdd t)).symm
  have hnull : μ (L a) = 0 := hμ (wild_line_null ν hν ha)
  have hnot : ∀ᵐ d ∂μ, d ∉ L a := (measure_eq_zero_iff_ae_notMem).mp hnull
  have hf : ∀ᵐ _d ∂μ, False := by
    filter_upwards [hL, hnot] with d hl hn
    exact hn hl
  apply Measure.measure_univ_eq_zero.mp
  simpa only [ae_iff, not_false_eq_true, Set.ofPred_true] using hf

end PlaneFiveColor.Spectral

end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_InvariantMean
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
/-! A discrete abelian invariant mean, constructed from weighted cube
averages. Repeated group elements keep their multiplicities. -/
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
namespace PlaneFiveColor.InvariantMean

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

lemma cmean_const (z : ℂ) : cmean (BoundedContinuousFunction.const G z) = z := by
  have hr : realPart (BoundedContinuousFunction.const G z) = BoundedContinuousFunction.const G z.re := rfl
  have hi : imagPart (BoundedContinuousFunction.const G z) = BoundedContinuousFunction.const G z.im := rfl
  simp only [cmean, hr, hi, mean_const, Complex.re_add_im]

lemma cmean_shift (g : G) (f : G →ᵇ ℂ) : cmean (cshift g f) = cmean f := by
  have hr : realPart (cshift g f) = shift g (realPart f) := rfl
  have hi : imagPart (cshift g f) = shift g (imagPart f) := rfl
  simp only [cmean, hr, hi, mean_shift]

open MeasureTheory AddCircle

/-- An ordinary nonconstant Fourier monomial has zero mean as soon as its
half-period is represented in the discrete group. -/
lemma circleMean_fourier_nonzero (ρ : G →+ UnitAddCircle) {n : ℤ} (hn : n ≠ 0)
    (hρ : ∃ g, ρ g = ((1 / 2 / n : ℝ) : UnitAddCircle)) : circleMean ρ (fourier n) = 0 := by
  obtain ⟨g, hg⟩ := hρ
  have he : cshift g (circlePull ρ (fourier n)) = -(circlePull ρ (fourier n)) := by
    ext x
    simp only [cshift_apply, circlePull_apply, map_add, hg, BoundedContinuousFunction.neg_apply]
    exact fourier_add_half_inv_index hn zero_lt_one _
  have hm := cmean_shift g (circlePull ρ (fourier n))
  rw [he] at hm
  have hn' : cmean (-circlePull ρ (fourier n)) = -cmean (circlePull ρ (fourier n)) :=
    cmeanCLM.map_neg _
  rw [hn'] at hm
  apply neg_eq_self.mp at hm
  exact hm

theorem circleMean_eq_integral (ρ : G →+ UnitAddCircle)
    (hρ : ∀ n : ℤ, n ≠ 0 → ∃ g, ρ g = ((1 / 2 / n : ℝ) : UnitAddCircle))
    (f : C(UnitAddCircle, ℂ)) : cmean (circlePull ρ f) = ∫ x, f x ∂haarAddCircle := by
  have he : circleMean ρ = circleIntegral := by
    apply ContinuousLinearMap.ext_on (s := Set.range (@fourier 1))
    · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
    · rintro _ ⟨n, rfl⟩
      by_cases hn : n = 0
      · subst n
        have hp : circlePull ρ (fourier 0) = BoundedContinuousFunction.const G 1 := by
          ext x; simp
        simp only [circleMean_apply, hp, cmean_const, circleIntegral_apply]
        simp
      · rw [circleMean_fourier_nonzero ρ hn (hρ n hn), circleIntegral_apply]
        exact (integral_eq_zero_of_add_right_eq_neg
          (fourier_add_half_inv_index hn zero_lt_one)).symm
  exact DFunLike.congr_fun he f

lemma periodMap_half_period (n : ℤ) : ∃ g, periodMap g = ((1 / 2 / n : ℝ) : UnitAddCircle) := by
  refine ⟨QuotientAddGroup.mk (1 / 2 / n : AF), ?_⟩
  rw [periodMap_apply]
  congr 1

/-- The exact identification of the chosen mean on ordinary continuous
periodic functions asserted in spectral.tex113–123. -/
theorem ordinary_mean_integral (f : C(UnitAddCircle, ℂ)) :
    cmean (circlePull periodMap f) = ∫ x, f x ∂haarAddCircle :=
  circleMean_eq_integral periodMap (fun n _ => periodMap_half_period n) f

section WeakMean
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma weakMean_pair (V : G →ᵇ H) (v : H) :
    inner ℝ (weakMean V) v = mean (pairing V v) :=
  InnerProductSpace.toDual_symm_apply

lemma weakMean_norm_bound (V : G →ᵇ H) : ‖weakMean V‖ ≤ mean (normFn V) := by
  rw [weakMean, LinearIsometryEquiv.norm_map]
  apply (pairingMean V).opNorm_le_bound (mean_nonneg _ (fun x => by rw [normFn_apply]; exact norm_nonneg _))
  intro v
  change |mean (pairing V v)| ≤ mean (normFn V) * ‖v‖
  simpa only [mul_comm] using pairing_mean_bound V v

lemma weakMean_sub (V W : G →ᵇ H) : weakMean (V-W) = weakMean V - weakMean W := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_sub_left, weakMean_pair, weakMean_pair, weakMean_pair]
  have he : pairing (V-W) v = pairing V v - pairing W v := by
    ext x; simp [inner_sub_right]
  rw [he]
  exact meanCLM.map_sub _ _

lemma weakMean_shift (V : G →ᵇ H) (g : G) :
    weakMean (V.compContinuous ⟨fun x => x+g, continuous_of_discreteTopology⟩) = weakMean V := by
  apply ext_inner_right ℝ
  intro v
  rw [weakMean_pair, weakMean_pair]
  exact mean_shift g (pairing V v)

lemma weakMean_map {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [CompleteSpace J] (L : H →L[ℝ] J) (V : G →ᵇ H) :
    weakMean (L.compLeftContinuousBounded G V) = L (weakMean V) := by
  apply ext_inner_right ℝ
  intro v
  rw [weakMean_pair, ← L.adjoint_inner_right, weakMean_pair]
  congr 1
  ext x
  exact (L.adjoint_inner_left (V x) v).symm

end WeakMean

section Periodization
variable {H : Type*} [NormedAddCommGroup H]

/-- Absolute finiteness of each period sum. -/
lemma period_summable {h : AF → H} {N : ℕ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0) (t : AF) :
    Summable (fun k : ℤ => h (t+k)) := by
  obtain ⟨M, hM⟩ := exists_nat_gt |(t : ℝ)|
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc
    (-((N+M : ℕ) : ℤ)-2) (((N+M : ℕ) : ℤ)+2)))
  intro k hk
  by_contra hn
  apply hk
  apply hs
  simp only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hn
  change (N : ℝ) < |(t : ℝ)+(k : ℝ)|
  have hM1 := (abs_lt.mp hM).1
  have hM2 := (abs_lt.mp hM).2
  rcases hn with hn | hn
  · have hk' : (k : ℝ) < -((N : ℝ)+M)-2 := by exact_mod_cast hn
    rw [abs_of_neg] <;> linarith
  · have hk' : (N : ℝ)+M+2 < (k : ℝ) := by exact_mod_cast hn
    rw [abs_of_pos] <;> linarith

lemma periodSum_shift (h : AF → H) (s t : AF) :
    periodSum (fun x => h (x+s)) t = periodSum h (t+s) := by
  unfold periodSum
  congr 1
  ext k
  abel_nf

lemma periodBCF_norm_le (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (hB : 0 ≤ B) :
    ‖periodBCF h hs hb‖ ≤ (Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B := by
  apply BoundedContinuousFunction.norm_le (mul_nonneg (Nat.cast_nonneg _) hB) |>.mpr
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact periodSum_norm_le hs hb t

lemma integralReal_mono (h j : AF → ℝ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → j t = 0)
    (jb : ∀ t, ‖j t‖ ≤ C) (hle : ∀ t, h t ≤ j t) :
    integralReal h hs hb ≤ integralReal j js jb := by
  apply mean_mono
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact (period_summable hs t).tsum_le_tsum (fun k => hle (t+k)) (period_summable js t)

variable [InnerProductSpace ℝ H] [CompleteSpace H]

lemma weakIntegral_norm_bound (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (hB : 0 ≤ B) :
    ‖weakIntegral h hs hb‖ ≤ (Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B := by
  apply (weakMean_norm_bound _).trans
  rw [← mean_const (G := PeriodGroup) ((Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B)]
  apply mean_mono
  intro x
  exact ((periodBCF h hs hb).norm_coe_le_norm x).trans (periodBCF_norm_le h hs hb hB)

lemma weakIntegral_shift (h : AF → H) (s : AF) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (hss : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → h (t+s) = 0)
    (hbs : ∀ t, ‖h (t+s)‖ ≤ C) :
    weakIntegral (fun t => h (t+s)) hss hbs = weakIntegral h hs hb := by
  have he : periodBCF (fun t => h (t+s)) hss hbs =
      (periodBCF h hs hb).compContinuous
        (⟨fun x : PeriodGroup => x+periodMk s,
          continuous_of_discreteTopology⟩) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact periodSum_shift h s t
  unfold weakIntegral
  rw [he, weakMean_shift]

lemma weakIntegral_sub (h j : AF → H) {N M L : ℕ} {B C Q : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → j t = 0)
    (jb : ∀ t, ‖j t‖ ≤ C)
    (ds : ∀ t : AF, (L : ℝ) < |(t : ℝ)| → h t-j t = 0)
    (db : ∀ t, ‖h t-j t‖ ≤ Q) :
    weakIntegral (fun t => h t-j t) ds db = weakIntegral h hs hb - weakIntegral j js jb := by
  have he : periodBCF (fun t => h t-j t) ds db = periodBCF h hs hb - periodBCF j js jb := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact (period_summable hs t).tsum_sub (period_summable js t)
  unfold weakIntegral
  rw [he, weakMean_sub]

lemma weakIntegral_map {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [CompleteSpace J] (L : H →L[ℝ] J) (h : AF → H) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → L (h t) = 0)
    (jb : ∀ t, ‖L (h t)‖ ≤ C) :
    weakIntegral (fun t => L (h t)) js jb = L (weakIntegral h hs hb) := by
  have he : periodBCF (fun t => L (h t)) js jb =
      L.compLeftContinuousBounded PeriodGroup (periodBCF h hs hb) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact (L.map_tsum (period_summable hs t)).symm
  unfold weakIntegral
  rw [he, weakMean_map]

end Periodization
section OrdinaryIntegral
open ContinuousMap TopologicalSpace

/-- Compact support makes all local norm sums finite, before any interchange
of sums, evaluations or integrals. -/
lemma compact_local_summable (f : C(ℝ, ℂ)) {N : ℕ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (K : Compacts ℝ) :
    Summable (fun k : ℤ => ‖(f.comp (ContinuousMap.addRight k)).restrict K‖) := by
  obtain ⟨C, hC⟩ := K.isCompact.isBounded.exists_norm_le
  obtain ⟨M, hM⟩ := exists_nat_gt C
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc
    (-((N+M : ℕ) : ℤ)-2) (((N+M : ℕ) : ℤ)+2)))
  intro k hk
  by_contra hn
  apply hk
  rw [norm_eq_zero]
  ext x
  apply hs
  change (N : ℝ) < |(x : ℝ)+(k : ℝ)|
  have hx : |(x : ℝ)| < (M : ℝ) := lt_of_le_of_lt (hC x x.property) hM
  simp only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hn
  have hx1 := (abs_lt.mp hx).1
  have hx2 := (abs_lt.mp hx).2
  rcases hn with hn | hn
  · have hk' : (k : ℝ) < -((N : ℝ)+M)-2 := by exact_mod_cast hn
    rw [abs_of_neg] <;> linarith
  · have hk' : (N : ℝ)+M+2 < (k : ℝ) := by exact_mod_cast hn
    rw [abs_of_pos] <;> linarith

lemma ordinaryPeriod_apply (f : C(ℝ, ℂ)) {N : ℕ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (t : ℝ) :
    ordinaryPeriod f (t : UnitAddCircle) = ∑' k : ℤ, f (t+k) := by
  change (∑' k : ℤ, f.comp (ContinuousMap.addRight (k • (1 : ℝ)) )) t = _
  have hf := ContinuousMap.summable_of_locally_summable_norm (compact_local_summable f hs)
  simpa only [zsmul_eq_mul, mul_one, ContinuousMap.comp_apply,
    ContinuousMap.addRight, ContinuousMap.coe_mk] using (ContinuousMap.tsum_apply hf t).symm

/-- Exact agreement of the manuscript's invariant integral with the usual
Lebesgue integral on every continuous boundedly supported test function. -/
theorem integralComplex_ordinary (f : C(ℝ, ℂ)) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (hb : ∀ t, ‖f t‖ ≤ B) :
    integralComplex (fun t : AF => f t) (fun t ht => hs t ht) (fun t => hb t) =
      ∫ t : ℝ, f t := by
  have he : periodBCF (fun t : AF => f t) (fun t ht => hs t ht) (fun t => hb t) =
      circlePull periodMap (ordinaryPeriod f) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      change (∑' k : ℤ, f ((t+k : AF) : ℝ)) = ordinaryPeriod f ((t : ℝ) : UnitAddCircle)
      rw [ordinaryPeriod_apply f hs]
      rfl
  unfold integralComplex
  rw [he, ordinary_mean_integral]
  have hf := Real.fourierCoeff_tsum_comp_add (compact_local_summable f hs) 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, Int.cast_zero,
    Real.fourier_real_eq_integral_exp_smul, mul_zero, zero_mul, Complex.exp_zero, Complex.ofReal_zero,
    ordinaryPeriod, ContinuousMap.coe_mk] using hf

lemma integralComplex_re (h : AF → ℂ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (rs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → (h t).re = 0)
    (rb : ∀ t, ‖(h t).re‖ ≤ C) :
    (integralComplex h hs hb).re = integralReal (fun t => (h t).re) rs rb := by
  have he : realPart (periodBCF h hs hb) = periodBCF (fun t => (h t).re) rs rb := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact Complex.reCLM.map_tsum (period_summable hs t)
  simp only [integralComplex, cmean, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_self, add_zero, he, integralReal]

theorem integralReal_ordinary (f : C(ℝ, ℝ)) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (hb : ∀ t, ‖f t‖ ≤ B) :
    integralReal (fun t : AF => f t) (fun t ht => hs t ht) (fun t => hb t) =
      ∫ t : ℝ, f t := by
  let fc : C(ℝ, ℂ) := ⟨fun t => (f t : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hcs : ∀ t : ℝ, (N : ℝ) < |t| → fc t = 0 := by
    intro t ht
    simp [fc, hs t ht]
  have hcb : ∀ t, ‖fc t‖ ≤ B := by
    intro t
    simpa only [fc, coe_mk, Complex.norm_real] using hb t
  have hi := integralComplex_ordinary fc hcs hcb
  have hre := congrArg Complex.re hi
  rw [integralComplex_re _ _ _ (fun t ht => hs t ht) (fun t => hb t)] at hre
  change integralReal (fun t : AF => f t) _ _ = (∫ t : ℝ, (f t : ℂ)).re at hre
  rw [integral_complex_ofReal] at hre
  exact hre

end OrdinaryIntegral

section Smoothing
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma weakIntegral_congr (h j : AF → H) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → j t = 0)
    (jb : ∀ t, ‖j t‖ ≤ C) (he : ∀ t, h t = j t) :
    weakIntegral h hs hb = weakIntegral j js jb := by
  unfold weakIntegral
  congr 1
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact tsum_congr (fun k => he (t+k))

lemma shifted_support {φ : AF → ℝ} {N : ℕ}
    (hφ : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (s : AF) (hs : |(s : ℝ)| ≤ 1) :
    ∀ t : AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → φ (t-s) = 0 := by
  intro t ht
  apply hφ
  have hi : |(t : ℝ)| ≤ |(t : ℝ)-(s : ℝ)| + |(s : ℝ)| := by
    simpa using abs_add_le ((t : ℝ)-(s : ℝ)) (s : ℝ)
  change (N : ℝ) < |(t : ℝ)-(s : ℝ)|
  push_cast at ht
  linarith

variable (U : AF → H ≃ₗᵢ[ℝ] H)

/-- Translation continuity of smoothing rests only on regularity of the scalar
window, not on any measurability of the discrete representation. -/
theorem smoothed_translation_bound
    (hu : ∀ s t v, U s (U t v) = U (s+t) v)
    (φ : AF → ℝ) {N : ℕ} {B C : ℝ}
    (hφ : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : H) (s : AF) (hs : |(s : ℝ)| ≤ 1)
    (hC : 0 ≤ C) (hd : ∀ t, |φ (t-s)-φ t| ≤ C) :
    ‖U s (smoothedVector U φ hφ hb v) - smoothedVector U φ hφ hb v‖ ≤
      (Finset.Icc (-((N+1 : ℕ) : ℤ)-2) (((N+1 : ℕ) : ℤ)+2)).card * (C * ‖v‖) := by
  let h : AF → H := fun t => φ t • U t v
  let j : AF → H := fun t => φ (t-s) • U t v
  have hh := smoothed_support U φ hφ v
  have bh := smoothed_bound U φ hb v
  have hj := smoothed_support U (fun t => φ (t-s)) (shifted_support hφ s hs) v
  have bj := smoothed_bound U (fun t => φ (t-s)) (fun t => hb (t-s)) v
  have dh : ∀ t : AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → j t-h t = 0 := by
    intro t ht
    change φ (t-s) • U t v - φ t • U t v = 0
    rw [hj t ht, hh t (by push_cast at ht; linarith), sub_self]
  have db : ∀ t, ‖j t-h t‖ ≤ C*‖v‖ := by
    intro t
    change ‖φ (t-s) • U t v - φ t • U t v‖ ≤ _
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, (U t).norm_map]
    exact mul_le_mul_of_nonneg_right (hd t) (norm_nonneg v)
  have kh : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → U s (h t) = 0 := by
    intro t ht
    change U s (φ t • U t v) = 0
    rw [hh t ht, map_zero]
  have kb : ∀ t, ‖U s (h t)‖ ≤ B*‖v‖ := by
    intro t
    rw [(U s).norm_map]
    exact bh t
  have je : ∀ t, j t = U s (h (t+(-s))) := by
    intro t
    simp only [j, h, map_smul, hu, sub_eq_add_neg]
    congr 2
    abel_nf
  have kjs : ∀ t : AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → U s (h (t+(-s))) = 0 := by
    intro t ht
    rw [← je]
    exact hj t ht
  have kjb : ∀ t, ‖U s (h (t+(-s)))‖ ≤ B*‖v‖ := by
    intro t
    rw [← je]
    exact bj t
  have ji : weakIntegral j hj bj = U s (weakIntegral h hh bh) := by
    calc
      _ = weakIntegral (fun t => U s (h (t+(-s)))) kjs kjb :=
        weakIntegral_congr _ _ _ _ _ _ je
      _ = weakIntegral (fun t => U s (h t)) kh kb :=
        weakIntegral_shift (fun t => U s (h t)) (-s) kh kb kjs kjb
      _ = U s (weakIntegral h hh bh) :=
        weakIntegral_map (U s).toContinuousLinearEquiv.toContinuousLinearMap h hh bh kh kb
  have di := weakIntegral_sub j h hj bj hh bh dh db
  change ‖U s (weakIntegral h hh bh) - weakIntegral h hh bh‖ ≤ _
  rw [← ji, ← di]
  exact weakIntegral_norm_bound _ dh db (mul_nonneg hC (norm_nonneg v))

/-- Every uniformly continuous compact window produces a strongly continuous
vector even for a completely discontinuous representation of the discrete F. -/
theorem smoothed_tendsto
    (hu : ∀ s t v, U s (U t v) = U (s+t) v)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hφ : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : H) :
    Tendsto (fun s : AF => U s
      (smoothedVector U (fun t => φ t) (fun t ht => hφ t ht) (fun t => hb t) v))
      (𝓝 0) (𝓝 (smoothedVector U (fun t => φ t)
        (fun t ht => hφ t ht) (fun t => hb t) v)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let Q : ℝ := (Finset.Icc (-((N+1 : ℕ) : ℤ)-2) (((N+1 : ℕ) : ℤ)+2)).card * ‖v‖
  have hQ : 0 ≤ Q := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg v)
  have hp : 0 < ε/(Q+1) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hc _ hp
  have hnorm : ∀ᶠ s : AF in 𝓝 0, ‖s‖ < min δ 1 :=
    (show Tendsto (fun s : AF => ‖s‖) (𝓝 0) (𝓝 (0 : ℝ)) by
      simpa using continuous_norm.tendsto (0 : AF)).eventually
        (eventually_lt_nhds (lt_min hδ zero_lt_one))
  filter_upwards [hnorm] with s hs
  have hsδ : |(s : ℝ)| < δ := (lt_min_iff.mp hs).1
  have hs1 : |(s : ℝ)| ≤ 1 := le_of_lt (lt_min_iff.mp hs).2
  have hdiff : ∀ t : AF, |φ ((t-s : AF) : ℝ) - φ t| ≤ ε/(Q+1) := by
    intro t
    apply le_of_lt
    apply hd
    change |(t : ℝ)-(s : ℝ)-(t : ℝ)| < δ
    rw [show (t : ℝ)-(s : ℝ)-(t : ℝ) = -(s : ℝ) by ring, abs_neg]
    exact hsδ
  have hbound := smoothed_translation_bound U hu (fun t => φ t)
    (fun t ht => hφ t ht) (fun t => hb t) v s hs1 hp.le hdiff
  rw [dist_zero_right]
  apply hbound.trans_lt
  have hr : Q * (ε/(Q+1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < Q+1)]
    nlinarith
  simpa only [Q, mul_assoc, mul_comm (ε/(Q+1)) ‖v‖] using hr

end Smoothing
end PlaneFiveColor.InvariantMean
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Multipliers
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualPolishSpace _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
namespace PlaneFiveColor.LpMultiplier
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma weight_measurable (v : Lp ℂ 2 μ) :
    AEMeasurable (fun x => ENNReal.ofReal (‖v x‖^2)) μ :=
  ((Lp.aestronglyMeasurable v).norm.pow 2).aemeasurable.ennreal_ofReal

lemma weight_ac (v : Lp ℂ 2 μ) : weight v ≪ μ :=
  withDensity_absolutelyContinuous _ _

lemma weight_eq_zero_iff (v : Lp ℂ 2 μ) : weight v = 0 ↔ v = 0 := by
  constructor
  · intro hz
    have he := (withDensity_eq_zero_iff (weight_measurable v)).mp hz
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [he] with x hx
    have hsq : ‖v x‖^2 = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (sq_nonneg _)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro hv
    apply (withDensity_eq_zero_iff (weight_measurable v)).mpr
    filter_upwards [Lp.eq_zero_iff_ae_eq_zero.mp hv] with x hx
    simp [hx]

lemma norm_mul_sub_sq (z w : ℂ) (hz : ‖z‖ = 1) :
    ‖z*w-w‖^2 = 2 * (‖w‖^2 * (1-z.re)) := by
  have he := Complex.normSq_sub z 1
  simp only [Complex.normSq_eq_norm_sq, hz, one_pow, map_one, mul_one] at he
  rw [show z*w-w = (z-1)*w by ring, norm_mul, mul_pow, he]
  ring

lemma lp_norm_sq_integral (v : Lp ℂ 2 μ) :
    (∫ x, ‖v x‖^2 ∂μ) = ‖v‖^2 := by
  have he := L2.inner_def (𝕜 := ℝ) v v
  simpa only [real_inner_self_eq_norm_sq] using he.symm

lemma weight_deviation (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    (∫ x, 1-(h x).re ∂weight v) = ‖mul h hm hn v - v‖^2 / 2 := by
  rw [weight, integral_withDensity_eq_integral_toReal_smul₀ (weight_measurable v)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ x, ‖(mul h hm hn v-v) x‖^2 /2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [mul_ae h hm hn v, Lp.coeFn_sub (mul h hm hn v) v] with x hx hy
      rw [hy, Pi.sub_apply, hx, norm_mul_sub_sq _ _ (hn x),
        ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
      ring
    _ = _ := by rw [integral_div, lp_norm_sq_integral]

end PlaneFiveColor.LpMultiplier

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped ENNReal

lemma lineU_apply (ν : Measure D) (a : E) (t : F) (v : Lp ℂ 2 ν) :
    lineU ν a t v = LpMultiplier.mul
      (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ))
      (lineCharacter_measurable a t).aestronglyMeasurable (fun _ => Circle.norm_coe _) v := rfl

lemma lineU_ae (ν : Measure D) (a : E) (t : F) (v : Lp ℂ 2 ν) :
    lineU ν a t v =ᵐ[ν] (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ) * v d) :=
  LpMultiplier.mul_ae _ (lineCharacter_measurable a t).aestronglyMeasurable
    (fun _ => Circle.norm_coe _) v

lemma lineU_add (ν : Measure D) (a : E) (s t : F) (v : Lp ℂ 2 ν) :
    lineU ν a s (lineU ν a t v) = lineU ν a (s+t) v := by
  apply Lp.ext
  filter_upwards [lineU_ae ν a s (lineU ν a t v), lineU_ae ν a t v,
    lineU_ae ν a (s+t) v] with d hs ht hst
  rw [hs, ht, hst]
  have he := congrArg (fun z : Circle => (z : ℂ))
    ((lineCharacter a d).map_mul (Multiplicative.ofAdd s) (Multiplicative.ofAdd t))
  change (lineCharacter a d (Multiplicative.ofAdd (s+t)) : ℂ) =
    (lineCharacter a d (Multiplicative.ofAdd s) : ℂ) *
      (lineCharacter a d (Multiplicative.ofAdd t) : ℂ) at he
  rw [he, mul_assoc]

lemma lineU_zero (ν : Measure D) (a : E) (v : Lp ℂ 2 ν) : lineU ν a 0 v = v := by
  apply Lp.ext
  filter_upwards [lineU_ae ν a 0 v] with d hd
  simpa using hd

lemma weighted_coeff (ν : Measure D) (a : E) (v : Lp ℂ 2 ν) (t : F) :
    ContinuousCharacters.coeff (LpMultiplier.weight v) (lineCharacter a) t =
      ‖lineU ν a t v-v‖^2/2 := by
  rw [lineU_apply]
  simpa only [ContinuousCharacters.coeff, ContinuousCharacters.deviation, pow_one]
    using LpMultiplier.weight_deviation
      (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ))
      (lineCharacter_measurable a t).aestronglyMeasurable (fun _ => Circle.norm_coe _) v

/-- A wild law has no nonzero strongly continuous vector for any nonzero
algebraic line. The arbitrary L² vector is handled by its actual |v|² weight. -/
theorem strong_vector_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0) (v : Lp ℂ 2 ν)
    (hc : Tendsto (fun t => lineU ν a t v) (𝓝 0) (𝓝 v)) : v = 0 := by
  have hcoef : ContinuousAt
      (ContinuousCharacters.coeff (LpMultiplier.weight v) (lineCharacter a)) 0 := by
    have he : ContinuousCharacters.coeff (LpMultiplier.weight v) (lineCharacter a) =
        fun t => ‖lineU ν a t v-v‖^2/2 := funext (weighted_coeff ν a v)
    rw [he]
    change Tendsto _ (𝓝 0) (𝓝 (_ / 2))
    have hh := ((hc.sub (tendsto_const_nhds (x := v))).norm.pow 2).div_const 2
    simpa only [lineU_zero, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
      using hh
  exact (LpMultiplier.weight_eq_zero_iff v).mp
    (wild_continuous_coefficient_zero ν (LpMultiplier.weight v) hν
      (LpMultiplier.weight_ac v) ha hcoef)

/-- Every ordinary compact window has zero weak vector average along a
nonzero algebraic line of a wild law. -/
theorem wild_smoothed_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : Lp ℂ 2 ν) :
    InvariantMean.smoothedVector (lineU ν a) (fun t => φ t)
      (fun t ht => hs t ht) (fun t => hb t) v = 0 := by
  apply strong_vector_zero ν hν ha
  exact InvariantMean.smoothed_tendsto (lineU ν a) (lineU_add ν a) φ hc hs hb v

end PlaneFiveColor.Spectral

namespace PlaneFiveColor.InvariantMean
open MeasureTheory
lemma weakMean_complex {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [DiscreteTopology G] (V : G →ᵇ ℂ) : weakMean V = cmean V := by
  have hr := weakMean_pair V (1 : ℂ)
  have hi := weakMean_pair V Complex.I
  have hpr : pairing V (1 : ℂ) = realPart V := by
    ext x
    simp [pairing_apply, real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  have hpi : pairing V Complex.I = imagPart V := by
    ext x
    simp [pairing_apply, real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  rw [hpr] at hr
  rw [hpi] at hi
  apply Complex.ext <;>
    simp_all [real_inner_eq_re_inner ℂ, RCLike.inner_apply, cmean]

lemma weakIntegral_complex (h : AF → ℂ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : weakIntegral h hs hb = integralComplex h hs hb :=
  weakMean_complex _
end PlaneFiveColor.InvariantMean

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped ENNReal

lemma lineFourier_inner (ν : Measure D) [IsProbabilityMeasure ν] (a : E) (t : F) :
    inner ℂ (Lp.const 2 ν (1 : ℂ)) (lineU ν a t (Lp.const 2 ν (1 : ℂ))) =
      lineFourier ν a t := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lineU_ae ν a t (Lp.const 2 ν (1 : ℂ)),
    Lp.coeFn_const (2 : ℝ≥0∞) ν (1 : ℂ)] with d hu hc
  simp [hu, RCLike.inner_apply]

/-- The invariant scalar Fourier average on a nonzero algebraic line vanishes
for every real ordinary compact window; no measurability of t ↦ fν(at). -/
theorem wild_line_average_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) :
    InvariantMean.integralComplex
      (fun t : F => (φ t : ℂ) * lineFourier ν a t)
      (fun t ht => by rw [hs t ht, Complex.ofReal_zero, zero_mul])
      (fun t => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_of_le_one_right (abs_nonneg _) (lineFourier_norm_le ν a t)).trans (hb t)) = 0 := by
  let v := Lp.const 2 ν (1 : ℂ)
  let L : Lp ℂ 2 ν →L[ℝ] ℂ := (innerSL ℂ v).restrictScalars ℝ
  have he (t : F) : L (φ t • lineU ν a t v) = (φ t : ℂ) * lineFourier ν a t := by
    rw [map_smul]
    change φ t • inner ℂ v (lineU ν a t v) = _
    rw [lineFourier_inner]
    rfl
  have hjs : ∀ t : F, (N : ℝ) < |(t : ℝ)| → L (φ t • lineU ν a t v) = 0 := by
    intro t ht
    rw [he, hs t ht, Complex.ofReal_zero, zero_mul]
  have hjb : ∀ t : F, ‖L (φ t • lineU ν a t v)‖ ≤ B := by
    intro t
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (lineFourier_norm_le ν a t)).trans (hb t)
  have hm := InvariantMean.weakIntegral_map L
    (fun t : F => φ t • lineU ν a t v)
    (InvariantMean.smoothed_support (lineU ν a) (fun t => φ t) (fun t ht => hs t ht) v)
    (InvariantMean.smoothed_bound (lineU ν a) (fun t => φ t) (fun t => hb t) v)
    hjs hjb
  change InvariantMean.weakIntegral _ _ _ = L (InvariantMean.smoothedVector
    (lineU ν a) (fun t : F => φ t) (fun t ht => hs t ht) (fun t => hb t) v) at hm
  rw [wild_smoothed_zero ν hν ha φ hc hs hb v, map_zero] at hm
  rw [← InvariantMean.weakIntegral_complex]
  exact (InvariantMean.weakIntegral_congr _ _ _ _ hjs hjb (fun t => (he t).symm)).trans hm

end PlaneFiveColor.Spectral
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_FourierTests
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualPolishSpace _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace PlaneFiveColor.InvariantMean
open scoped BigOperators
open MeasureTheory Filter Topology

lemma integralReal_congr (f g : AF → ℝ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → f t = 0)
    (hb : ∀ t, ‖f t‖ ≤ B)
    (gs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → g t = 0)
    (gb : ∀ t, ‖g t‖ ≤ C) (he : ∀ t, f t = g t) :
    integralReal f hs hb = integralReal g gs gb := by
  unfold integralReal
  congr 1
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H t => simp only [periodBCF_mk, periodSum, he]

lemma integralReal_mul (f : AF → ℝ) (c : ℝ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → f t = 0)
    (hb : ∀ t, ‖f t‖ ≤ B)
    (gs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → c*f t = 0)
    (gb : ∀ t, ‖c*f t‖ ≤ C) :
    integralReal (fun t => c*f t) gs gb = c * integralReal f hs hb := by
  have he : periodBCF (fun t => c*f t) gs gb = c • periodBCF f hs hb := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      change (∑' k : ℤ, c * f (t+k)) = c * (∑' k : ℤ, f (t+k))
      exact tsum_mul_left
  exact (congrArg mean he).trans (mean_smul _ _)

lemma integralReal_sum {ι : Type*} (s : Finset ι) (f : ι → AF → ℝ)
    {N M : ℕ} {B : ι → ℝ} {C : ℝ}
    (hs : ∀ i, ∀ t : AF, (N : ℝ) < |(t : ℝ)| → f i t = 0)
    (hb : ∀ i t, ‖f i t‖ ≤ B i)
    (gs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → (∑ i ∈ s, f i t) = 0)
    (gb : ∀ t, ‖∑ i ∈ s, f i t‖ ≤ C) :
    integralReal (fun t => ∑ i ∈ s, f i t) gs gb =
      ∑ i ∈ s, integralReal (f i) (hs i) (hb i) := by
  have he : periodBCF (fun t => ∑ i ∈ s, f i t) gs gb =
      ∑ i ∈ s, periodBCF (f i) (hs i) (hb i) := by
    ext x
    rw [BoundedContinuousFunction.sum_apply]
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      simp only [periodBCF_mk, periodSum]
      exact Summable.tsum_finsetSum (fun i _ => period_summable (hs i) t)
  unfold integralReal
  rw [he]
  exact map_sum (meanCLM (G := PeriodGroup)) _ _

/-- Positivity of the literal invariant integral supplies a common small
parameter for finitely many nonnegative tests. This makes no ordinary
measurability assumption on any test. -/
theorem exists_small_nonnegative_tests {ι : Type*} (s : Finset ι)
    (φ : AF → ℝ) (f : ι → AF → ℝ) {N : ℕ} {B ε : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (hb : ∀ t, ‖φ t‖ ≤ B) (hp : ∀ t, 0 ≤ φ t)
    (hI : 0 < integralReal φ hs hb) (hε : 0 < ε)
    (hf : ∀ i t, 0 ≤ f i t ∧ f i t ≤ 1)
    (hz : ∀ i, integralReal (fun t => φ t * f i t)
      (fun t ht => by rw [hs t ht, zero_mul])
      (weighted_bound φ (f i) hb (hf i)) = 0) :
    ∃ t : AF, 0 < φ t ∧ ∀ i ∈ s, f i t < ε := by
  classical
  by_contra hn
  push Not at hn
  let g : AF → ℝ := fun t => ∑ i ∈ s, φ t * f i t
  have gs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → g t = 0 := by
    intro t ht
    simp [g, hs t ht]
  have gb : ∀ t, ‖g t‖ ≤ (s.card : ℝ) * B := by
    intro t
    calc
      _ ≤ ∑ i ∈ s, ‖φ t*f i t‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum (fun i _ => weighted_bound φ (f i) hb (hf i) t)
      _ = _ := by simp
  have gi : integralReal g gs gb = 0 := by
    rw [integralReal_sum s (fun i t => φ t*f i t)
      (fun i t ht => by rw [hs t ht, zero_mul])
      (fun i => weighted_bound φ (f i) hb (hf i)) gs gb]
    simp only [hz, Finset.sum_const_zero]
  have cs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → ε*φ t = 0 := by
    intro t ht; rw [hs t ht, mul_zero]
  have cb : ∀ t, ‖ε*φ t‖ ≤ |ε| * B := by
    intro t
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb t) (abs_nonneg _)
  have hle : ∀ t, ε*φ t ≤ g t := by
    intro t
    by_cases ht : 0 < φ t
    · obtain ⟨i, hi, hfi⟩ := hn t ht
      have hterm : φ t*f i t ≤ g t :=
        Finset.single_le_sum (fun j _ => mul_nonneg (hp t) (hf j t).1) hi
      exact (by nlinarith : ε*φ t ≤ φ t*f i t).trans hterm
    · have hφ : φ t = 0 := le_antisymm (le_of_not_gt ht) (hp t)
      simp [g, hφ]
  have hmono := integralReal_mono (fun t => ε*φ t) g cs cb gs gb hle
  rw [integralReal_mul φ ε hs hb cs cb, gi] at hmono
  exact (not_le_of_gt (mul_pos hε hI)) hmono

end PlaneFiveColor.InvariantMean

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped BigOperators
open InvariantMean

lemma lineFourier_re_le_one (ν : Measure D) [IsProbabilityMeasure ν] (a : E) (t : F) :
    (lineFourier ν a t).re ≤ 1 :=
  (Complex.re_le_norm _).trans (lineFourier_norm_le ν a t)

/-- Real part of the checked vanishing line average, with the same invariant
integral and the same compact window. -/
lemma wild_line_average_re_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) :
    integralReal (fun t : F => φ t * (lineFourier ν a t).re)
      (fun t ht => by rw [hs t ht, zero_mul])
      (fun t => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact (mul_le_of_le_one_right (abs_nonneg _)
          ((Complex.abs_re_le_norm _).trans (lineFourier_norm_le ν a t))).trans (hb t)) = 0 := by
  let f : F → ℂ := fun t => (φ t : ℂ) * lineFourier ν a t
  have fs : ∀ t : F, (N : ℝ) < |(t : ℝ)| → f t = 0 := by
    intro t ht; simp [f, hs t ht]
  have fb : ∀ t, ‖f t‖ ≤ B := by
    intro t
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (lineFourier_norm_le ν a t)).trans (hb t)
  have rs : ∀ t : F, (N : ℝ) < |(t : ℝ)| → (f t).re = 0 := by
    intro t ht; rw [fs t ht]; rfl
  have rb : ∀ t, ‖(f t).re‖ ≤ B := by
    intro t
    simpa only [Real.norm_eq_abs] using (Complex.abs_re_le_norm (f t)).trans (fb t)
  have hz : integralReal (fun t => (f t).re) rs rb = 0 := by
    rw [← integralComplex_re f fs fb rs rb]
    rw [show integralComplex f fs fb = 0 from wild_line_average_zero ν hν ha φ hc hs hb]
    rfl
  exact (integralReal_congr _ _ _ _ rs rb (fun t => by simp [f])).trans hz

/-- A compact tent window strictly inside the requested parameter radius. -/
lemma exists_positive_window {r : ℝ} (hr : 0 < r) :
    ∃ (φ : C(ℝ, ℝ)) (N : ℕ) (B : ℝ),
      (∀ t : ℝ, (N : ℝ) < |t| → φ t = 0) ∧
      (∀ t, ‖φ t‖ ≤ B) ∧ (∀ t, 0 ≤ φ t) ∧
      UniformContinuous φ ∧ (0 < ∫ t : ℝ, φ t) ∧
      (∀ t, 0 < φ t → |t| < r) := by
  let φ : C(ℝ, ℝ) := ⟨fun t => max 0 (r-|t|), by fun_prop⟩
  have hp (t : ℝ) : 0 ≤ φ t := le_max_left _ _
  have hb (t : ℝ) : ‖φ t‖ ≤ r := by
    rw [Real.norm_of_nonneg (hp t)]
    exact max_le hr.le (sub_le_self _ (abs_nonneg _))
  have houtside (t : ℝ) (ht : r ≤ |t|) : φ t = 0 := max_eq_left (sub_nonpos.mpr ht)
  have hcomp : HasCompactSupport φ := by
    apply HasCompactSupport.intro' (K := Set.Icc (-r) r) isCompact_Icc isClosed_Icc
    intro t ht
    apply houtside
    by_contra hn
    exact ht (abs_le.mp (le_of_lt (lt_of_not_ge hn)))
  have hi : 0 < ∫ t : ℝ, φ t :=
    φ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcomp hp
      (show φ 0 ≠ 0 by simpa [φ, max_eq_right hr.le] using hr.ne')
  obtain ⟨N, hN⟩ := exists_nat_gt r
  refine ⟨φ, N, r, (fun t ht => houtside t (le_of_lt (hN.trans ht))), hb, hp,
    hcomp.uniformContinuous_of_continuous φ.continuous, hi, ?_⟩
  intro t ht
  by_contra hn
  rw [houtside t (le_of_not_gt hn)] at ht
  exact lt_irrefl _ ht

theorem exists_small_wild_parameter {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (ν : Measure D) [IsProbabilityMeasure ν] (hν : IsWild ν)
    (a : ι → E) (ha : ∀ i, a i ≠ 0)
    (hn : ∀ i t, 0 ≤ (lineFourier ν (a i) t).re)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ t : F, t ≠ 0 ∧ |(t : ℝ)| < r ∧
      ∀ i ∈ s, (lineFourier ν (a i) t).re < ε := by
  obtain ⟨φ, N, B, hs, hb, hp, hc, hi, hradius⟩ := exists_positive_window hr
  have hz := fun i => wild_line_average_re_zero ν hν (ha i) φ hc hs
    (fun t => by simpa only [← Real.norm_eq_abs] using hb t)
  have hI : 0 < integralReal (fun t : F => φ t)
      (fun t ht => hs t ht) (fun t => hb t) := by
    rw [integralReal_ordinary φ hs hb]
    exact hi
  obtain ⟨t, ht, htest⟩ := exists_small_nonnegative_tests s
    (fun t : F => φ t) (fun i t => (lineFourier ν (a i) t).re)
    (fun t ht => hs t ht) (fun t => hb t) (fun t => hp t) hI hε
    (fun i t => ⟨hn i t, lineFourier_re_le_one ν (a i) t⟩)
    (fun i => by convert hz i using 1)
  refine ⟨t, ?_, hradius t ht, htest⟩
  intro he
  obtain ⟨i, his⟩ := hne
  have hh := htest i his
  rw [he, lineFourier_zero, Complex.one_re] at hh
  exact (not_lt_of_ge hε1) hh

end PlaneFiveColor.Spectral

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
namespace EuclideanFiveColor.DifferenceFourier

variable {G Y : Type*} [MeasurableSpace G] [MeasurableSpace Y]
  [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G]

variable (χ : G →* Circle)

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma coe_character_div (d e : G) :
    (χ (d / e) : ℂ) = (χ d : ℂ) * conj (χ e : ℂ) := by
  rw [map_div, div_eq_mul_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]

omit [MeasurableMul₂ G] [MeasurableInv G] in
lemma independent_coefficient (κ : Measure G) [IsProbabilityMeasure κ] :
    (∫ p : G × G, (χ (p.1 / p.2) : ℂ) ∂κ.prod κ) =
      (‖∫ d, (χ d : ℂ) ∂κ‖ ^ 2 : ℝ) := by
  calc
    _ = ∫ p : G × G, (χ p.1 : ℂ) * conj (χ p.2 : ℂ) ∂κ.prod κ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun p => coe_character_div χ p.1 p.2))
    _ = (∫ d, (χ d : ℂ) ∂κ) * (∫ d, conj (χ d : ℂ) ∂κ) := by
      convert integral_prod_mul (fun d => (χ d : ℂ)) (fun d => conj (χ d : ℂ)) using 1 <;> infer_instance
    _ = _ := by rw [integral_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma difference_coefficient (hχ : Measurable (fun d => (χ d : ℂ))) (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] :
    (∫ d, (χ d : ℂ) ∂differenceLaw ν κ) =
      ((∫ y, (‖∫ d, (χ d : ℂ) ∂κ y‖ ^ 2 : ℝ) ∂ν : ℝ) : ℂ) := by
  have hm := hχ
  have hdiv : Measurable (fun p : G × G => p.1 / p.2) :=
    measurable_fst.div measurable_snd
  rw [differenceLaw, integral_map hdiv.aemeasurable hm.aestronglyMeasurable,
    Measure.comp_eq_comp_const_apply]
  rw [Kernel.integral_comp]
  · simp only [Kernel.const_apply, Kernel.prod_apply]
    change (∫ y, (∫ p : G × G, (χ (p.1 / p.2) : ℂ) ∂(κ y).prod (κ y)) ∂ν) = _
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => independent_coefficient χ (κ y))
  · exact Integrable.of_bound (hm.comp hdiv).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun _ => (Circle.norm_coe _).le))

end EuclideanFiveColor.DifferenceFourier

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_ConditionalSpectrum
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor
open scoped BigOperators ComplexConjugate

lemma lineFourier_eq (ν : Measure D) (a : E) (t : F) :
    lineFourier ν a t = ∫ d, (eval (a * ofF t) d : ℂ) ∂ν := rfl

end

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Approximation
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.Spectral.K_countable _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.PlaneFiveColor.Spectral.rotErgodic _root_.OAI.PlaneFiveColor.Spectral.rotInvariant _root_.OAI.PlaneFiveColor.Spectral.rotMeasurable _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal

open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.DifferenceInvariant
variable {G Y : Type*} [CommGroup G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSpace Y]

lemma invariant (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ]
    (R : Y → Y) (hR : MeasurePreserving R ν ν)
    (T : G →* G) (hT : Measurable T)
    (he : ∀ᵐ y ∂ν, κ (R y) = (κ y).map T) :
    MeasurePreserving T (differenceLaw ν κ) (differenceLaw ν κ) := by
  have hprod : (((κ ×ₖ κ) ∘ₘ ν).map (Prod.map T T)) = ((κ ×ₖ κ) ∘ₘ ν) := by
    ext s hs
    rw [Measure.map_apply (hT.prodMap hT) hs,
      Measure.bind_apply ((hT.prodMap hT) hs) (κ ×ₖ κ).aemeasurable,
      Measure.bind_apply hs (κ ×ₖ κ).aemeasurable]
    calc
      (∫⁻ y, (κ ×ₖ κ) y ((Prod.map T T) ⁻¹' s) ∂ν) =
          ∫⁻ y, (κ ×ₖ κ) (R y) s ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [he] with y hy
        rw [Kernel.prod_apply, Kernel.prod_apply, hy,
          Measure.map_prod_map _ _ hT hT, Measure.map_apply (hT.prodMap hT) hs]
      _ = ∫⁻ y, (κ ×ₖ κ) y s ∂ν := hR.lintegral_comp (Kernel.measurable_coe _ hs)
  have hdiv : Measurable (fun p : G × G => p.1 / p.2) := measurable_fst.div measurable_snd
  refine ⟨hT, ?_⟩
  rw [differenceLaw, Measure.map_map hT hdiv]
  calc
    (((κ ×ₖ κ) ∘ₘ ν).map (T ∘ (fun p : G × G => p.1 / p.2))) =
        ((κ ×ₖ κ) ∘ₘ ν).map ((fun p : G × G => p.1 / p.2) ∘ Prod.map T T) := by
      congr 1
      funext p
      exact map_div T p.1 p.2
    _ = (((κ ×ₖ κ) ∘ₘ ν).map (Prod.map T T)).map (fun p : G × G => p.1 / p.2) :=
      (Measure.map_map hdiv (hT.prodMap hT)).symm
    _ = _ := by rw [hprod]

end EuclideanFiveColor.DifferenceInvariant

/-! The scalar finite bounded-module approximation in (source-4), and its
finite-vector consequence. All functions are measurable bounded representatives. -/

namespace EuclideanFiveColor.KernelSupport
open MeasureTheory
variable {K X Y : Type*} [Group K] [MeasurableSpace X] [MeasurableSpace Y]
  [MulAction K X] [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y]
lemma factor_smul_preserving (μ : Measure X) [SMulInvariantMeasure K X μ]
    (p : X → Y) (hp : Measurable p)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) (k : K) :
    MeasurePreserving (fun y : Y => k • y) (μ.map p) (μ.map p) := by
  refine ⟨measurable_const_smul k, ?_⟩
  rw [Measure.map_map (measurable_const_smul k) hp]
  calc
    μ.map ((fun y : Y => k • y) ∘ p) = μ.map (p ∘ (fun x : X => k • x)) :=
      Measure.map_congr ((hpe k).mono fun _ hx => hx.symm)
    _ = (μ.map (fun x : X => k • x)).map p :=
      (Measure.map_map hp (measurable_const_smul k)).symm
    _ = μ.map p := by rw [measurePreserving_smul k μ |>.map_eq]
end EuclideanFiveColor.KernelSupport

namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators ENNReal
variable {X Y W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
  [MulAction K X] [MulAction K Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

lemma relative_difference_invariant (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure K X μ] (b : X → D) (p : X → Y)
    (hb : Measurable b) (hp : Measurable p)
    (hbe : ∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) (k : K) :
    MeasurePreserving (fun d : D => k • d)
      (DifferenceFourier.differenceLaw (μ.map p) (condDistrib b p μ))
      (DifferenceFourier.differenceLaw (μ.map p) (condDistrib b p μ)) := by
  have he := KernelSupport.condDistrib_equivariant μ b p hb hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun d : D => k • d)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hbe k)
  haveI : IsProbabilityMeasure (μ.map p) := Measure.isProbabilityMeasure_map hp.aemeasurable
  exact DifferenceInvariant.invariant (μ.map p) (condDistrib b p μ)
    (fun y : Y => k • y) (KernelSupport.factor_smul_preserving μ p hp hpe k)
    (scalarHom (kCoeff k)) (measurable_const_smul k) he

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_BoundedFunctions
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.familyRealModule _root_.OAI.EuclideanFiveColor.BoundedMeasurable.instCoeFunFamilyForallFunc _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace EuclideanFiveColor.BoundedMeasurable

section
variable (X : Type*) [MeasurableSpace X]

variable {X}

variable (μ : Measure X) [IsFiniteMeasure μ]

lemma lp_congr (p : ℝ≥0∞) {f g : Func X} (h : f =ᵐ[μ] g) : lp μ p f = lp μ p g :=
  MemLp.toLp_congr _ _ h

lemma l2_eq_iff (f g : Func X) : l2 μ f = l2 μ g ↔ f =ᵐ[μ] g := by
  constructor
  · intro h
    exact (l2_ae μ f).symm.trans (h ▸ l2_ae μ g)
  · exact lp_congr μ 2

lemma inner_l2 (f g : Func X) :
    inner ℝ (l2 μ f) (l2 μ g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2_ae μ f, l2_ae μ g] with x hx hy
  rw [hx, hy]

end
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma norm_l2_sq (μ : Measure X) [IsFiniteMeasure μ] (f : Func X) :
    ‖l2 μ f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_l2]
  simp only [real_inner_self_eq_norm_sq]

variable [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq in
lemma conditional_integral (f : Func X) : ∫ y, conditional μ q f y ∂μ.map q = ∫ x, f x ∂μ :=
  ConditionalFiber.integral_fiber μ q hq f (integrable μ f)

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma project_integral (f : Func X) : ∫ x, project μ q hq f x ∂μ = ∫ x, f x ∂μ := by
  rw [← conditional_integral μ q hq f]
  exact (integral_map hq.aemeasurable (measurable (conditional μ q f)).aestronglyMeasurable).symm

end EuclideanFiveColor.BoundedMeasurable

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Factors
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EuclideanFiveColor
open MeasureTheory

namespace OrbitSpace
variable {K : Type*}

lemma continuous_val : Continuous (val : OrbitSpace K → K → ℂ) :=
  (equiv K).homeomorph.continuous
lemma continuous_mk : Continuous (mk : (K → ℂ) → OrbitSpace K) :=
  (equiv K).homeomorph.symm.continuous

instance instContinuousConstSMul [Monoid K] : ContinuousConstSMul K (OrbitSpace K) where
  continuous_const_smul k := continuous_mk.comp
    (continuous_pi fun l => (continuous_apply (l*k)).comp continuous_val)
instance instMeasurableConstSMul [Monoid K] : MeasurableConstSMul K (OrbitSpace K) where
  measurable_const_smul k := (continuous_const_smul k).measurable

end OrbitSpace

end EuclideanFiveColor

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_RelativeProducts
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open scoped RealInnerProductSpace BoundedContinuousFunction

namespace EuclideanFiveColor.RelativeProduct
open MeasureTheory ProbabilityTheory
variable {K X Y : Type*} [AddGroup K] [AddAction K X] [AddAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstVAdd K X] [MeasurableConstVAdd K Y]

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma conditional_covariance_add (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k +ᵥ x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k +ᵥ x) = k +ᵥ q x) (k : K) :
    ∀ᵐ y ∂μ.map q, condDistrib id q μ (k +ᵥ y) =
      (condDistrib id q μ y).map (fun x => k +ᵥ x) :=
  KernelSupport.condDistrib_equivariant μ id q measurable_id hq
    (MeasurableEquiv.vadd k) (MeasurableEquiv.vadd k) (fun x => k +ᵥ x)
    (measurable_const_vadd k) (hpres k) (hqcov k) (Filter.Eventually.of_forall fun _ => rfl)

end EuclideanFiveColor.RelativeProduct

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

lemma norm_project_l2 (f : Func X) :
    ‖l2 μ (project μ q hq f)‖ = ‖l2 (μ.map q) (conditional μ q f)‖ := by
  have : ‖l2 μ (project μ q hq f)‖^2 = ‖l2 (μ.map q) (conditional μ q f)‖^2 := by
    rw [norm_l2_sq, norm_l2_sq]
    exact (integral_map hq.aemeasurable
      ((measurable (conditional μ q f)).norm.pow_const 2).aestronglyMeasurable).symm
  nlinarith [norm_nonneg (l2 μ (project μ q hq f)),
    norm_nonneg (l2 (μ.map q) (conditional μ q f))]

end
section
variable {G X : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]

variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma l2_act (g : G) (f : Func X) :
    l2 μ (act g f) = Amenable.Koopman.action μ g (l2 μ f) := by
  apply Lp.ext
  exact (l2_ae μ (act g f)).trans ((MeasureTheory.measurePreserving_vadd g μ).quasiMeasurePreserving.ae_eq_comp
    (l2_ae μ f)).symm |>.trans (Amenable.Koopman.coe_action μ g (l2 μ f)).symm

end
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

variable {G : Type*} [AddCommGroup G] [AddAction G X] [AddAction G Y]
  [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y] [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, ∀ᵐ x ∂μ, q (g +ᵥ x) = g +ᵥ q x)

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq hqcov in
lemma conditional_act (g : G) (f : Func X) :
    conditional μ q (act g f) =ᵐ[μ.map q] act g (conditional μ q f) := by
  filter_upwards [RelativeProduct.conditional_covariance_add μ q hq
    (fun k => measurePreserving_vadd k μ) hqcov g] with y hy
  change (∫ x, f (g +ᵥ x) ∂condDistrib id q μ y) = ∫ x, f x ∂condDistrib id q μ (g +ᵥ y)
  rw [hy]
  exact (integral_map (measurable_const_vadd g).aemeasurable (measurable f).aestronglyMeasurable).symm

omit [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ] in
include hqcov in
lemma act_lift (g : G) (b : Func Y) :
    act g (comp b q hq) =ᵐ[μ] comp (act g b) q hq := by
  filter_upwards [hqcov g] with x hx
  simp only [act_apply, comp_apply, hx]

omit [StandardBorelSpace Y] [Nonempty Y] in
include hqcov in
lemma project_act (g : G) (f : Func X) :
    project μ q hq (act g f) =ᵐ[μ] act g (project μ q hq f) := by
  have he : project μ q hq (act g f) =ᵐ[μ] comp (act g (conditional μ q f)) q hq :=
    ae_of_ae_map hq.aemeasurable (conditional_act μ q hq hqcov g f)
  exact he.trans (act_lift μ q hq hqcov g _).symm

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal BoundedContinuousFunction

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Representations
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace EuclideanFiveColor.Koopman
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
lemma nonlinear_commute (s : X → X) (hs : MeasurePreserving s μ μ)
    {F : ℂ → ℂ} {c : ℝ≥0} (hF : LipschitzWith c F) (h0 : F 0 = 0) (v : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving s hs (hF.compLp h0 v) = hF.compLp h0 (Lp.compMeasurePreserving s hs v) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (hF.compLp h0 v) hs,
    hs.quasiMeasurePreserving.ae (hF.coeFn_compLp h0 v),
    hF.coeFn_compLp h0 (Lp.compMeasurePreserving s hs v),Lp.coeFn_compMeasurePreserving v hs] with x h1 h2 h3 h4
  simp only [Function.comp_apply,h1,h2,h3,h4]
end EuclideanFiveColor.Koopman
end

noncomputable section
open Filter Topology
namespace EuclideanFiveColor.ContinuousVectors
variable {A H : Type*} [AddCommGroup A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative A →* unitary (H →L[ℂ] H))
lemma op_add (a b : A) (v : H) : op U (a+b) v = op U a (op U b v) := by
  change ((U (Multiplicative.ofAdd a * Multiplicative.ofAdd b) : unitary _) : H →L[ℂ] H) v = _
  rw [map_mul]; rfl
lemma op_comm (a b : A) (v : H) : op U a (op U b v) = op U b (op U a v) := by
  rw [← op_add,← op_add,add_comm]
variable [TopologicalSpace A]
lemma op_mem (a : A) {v : H} (hv : v ∈ space U) : op U a v ∈ space U := by
  have ht := ((op U a).continuous.tendsto v).comp hv
  change Tendsto (fun z => op U z (op U a v)) (𝓝 0) (𝓝 (op U a v))
  simpa only [Function.comp_def,op_comm U a] using ht
variable [IsTopologicalAddGroup A]
lemma orbit_continuous {v : H} (hv : v ∈ space U) : Continuous (fun a => op U a v) := by
  rw [continuous_iff_continuousAt]
  intro a
  have ht0 : Tendsto (fun b : A => b-a) (𝓝 a) (𝓝 0) := by
    have hh := ((tendsto_id : Tendsto (fun b : A => b) (𝓝 a) (𝓝 a)).sub_const a)
    rw [sub_self] at hh
    exact hh
  have ht := (((op U a).continuous.tendsto v).comp hv).comp ht0
  change Tendsto (fun b => op U b v) (𝓝 a) (𝓝 (op U a v))
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ext b
  change op U b v = op U a (op U (b-a) v)
  rw [← op_add]
  congr 1
  abel_nf
end EuclideanFiveColor.ContinuousVectors
end

noncomputable section
open MeasureTheory
namespace PlaneFiveColor.LabelModel
open Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
variable (k : ℕ) (ω : Space k)
lemma rotation_apply (b : K) (v : Hilbert k ω) :
    (rotation k ω b : Hilbert k ω →L[ℂ] Hilbert k ω) v =
      Lp.compMeasurePreserving (rotate k b) (rotate_preserving k ω b) v := rfl
lemma op_apply (a : E) (v : Hilbert k ω) : op (representation k ω) a v =
    Lp.compMeasurePreserving (trans k a) (trans_preserving k ω a) v := rfl
lemma rotation_covariance (b : K) (a : E) (v : Hilbert k ω) :
    (rotation k ω b : Hilbert k ω →L[ℂ] Hilbert k ω) (op (representation k ω) a v) =
      op (representation k ω) (kCoeff b*a) ((rotation k ω b : Hilbert k ω →L[ℂ] Hilbert k ω) v) := by
  simp only [rotation_apply,op_apply,← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext x
  exact covariance k a b x
end PlaneFiveColor.LabelModel
end

noncomputable section
open scoped InnerProductSpace
namespace EuclideanFiveColor
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
lemma projection_fixed_of_contraction (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (F : H → H) (hF : LipschitzWith 1 F) (hS : ∀ v ∈ S, F v ∈ S)
    (v : H) (hv : F v = v) : F (S.starProjection v) = S.starProjection v := by
  let p := S.starProjection v
  have hp : p ∈ S := S.starProjection_apply_mem v
  have hh : ‖v-F p‖ ≤ ‖v-p‖ := by
    simpa only [hv,NNReal.coe_one,one_mul,dist_eq_norm] using hF.dist_le_mul v p
  have ho : ⟪v-p,p-F p⟫_ℂ = 0 := S.starProjection_inner_eq_zero v _ (S.sub_mem hp (hS p hp))
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v-p) (p-F p) ho
  rw [sub_add_sub_cancel] at he
  have hz : ‖p-F p‖ = 0 := by nlinarith [norm_nonneg (v-p),norm_nonneg (p-F p),norm_nonneg (v-F p)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace EuclideanFiveColor.ContinuousVectors
variable {A X : Type*} [AddCommGroup A] [TopologicalSpace A] [MeasurableSpace X]
  (μ : Measure X) (U : Multiplicative A →* unitary (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ))
  (s : A → X → X) (hs : ∀ a, MeasurePreserving (s a) μ μ)
  (hU : ∀ a v, op U a v = Lp.compMeasurePreserving (s a) (hs a) v)
include hU
lemma nonlinear_mem {F : ℂ → ℂ} {c : ℝ≥0} (hF : LipschitzWith c F) (h0 : F 0 = 0)
    {v : Lp ℂ 2 μ} (hv : v ∈ space U) : hF.compLp h0 v ∈ space U := by
  have ht := (hF.continuous_compLp h0).continuousAt.tendsto.comp hv
  change Tendsto (fun a => op U a (hF.compLp h0 v)) (𝓝 0) (𝓝 (hF.compLp h0 v))
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  simp only [Function.comp_apply,hU,Koopman.nonlinear_commute]
omit hU
lemma clamp_lipschitz : LipschitzWith 1 clamp := by
  have hr : LipschitzWith 1 (fun z : ℂ => z.re) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [NNReal.coe_one,one_mul,Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,← Complex.sub_re] using Complex.abs_re_le_norm (a-b)
  change LipschitzWith 1 (fun z : ℂ => ((max 0 (min 1 z.re) : ℝ) : ℂ))
  simpa only [one_mul,Function.comp_def] using Complex.isometry_ofReal.lipschitz.comp ((hr.const_min 1).const_max 0)
lemma clamp_range (z : ℂ) : (clamp z).im = 0 ∧ 0 ≤ (clamp z).re ∧ (clamp z).re ≤ 1 := by
  change (0 : ℝ) = 0 ∧ 0 ≤ max 0 (min 1 z.re) ∧ max 0 (min 1 z.re) ≤ 1
  exact ⟨rfl,le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩
lemma clamp_eq {z : ℂ} (hz : z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1) : clamp z = z := by
  rw [clamp,min_eq_right hz.2.2,max_eq_right hz.2.1]
  exact Complex.ext (by simp) (by simpa using hz.1.symm)
include hU
lemma projection_range (v : Lp ℂ 2 μ)
    (hv : ∀ᵐ x ∂μ, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) :
    ∀ᵐ x ∂μ, ((space U).starProjection v x).im = 0 ∧
      0 ≤ ((space U).starProjection v x).re ∧ ((space U).starProjection v x).re ≤ 1 := by
  have he : clamp_lipschitz.compLp clamp_zero v = v := by
    apply Lp.ext
    filter_upwards [clamp_lipschitz.coeFn_compLp clamp_zero v,hv] with x hx hvx
    exact hx.trans (clamp_eq hvx)
  have hp := projection_fixed_of_contraction (space U) (clamp_lipschitz.compLp clamp_zero)
    (clamp_lipschitz.lipschitzWith_compLp clamp_zero)
    (fun v hv => nonlinear_mem μ U s hs hU clamp_lipschitz clamp_zero hv) v he
  have hae := clamp_lipschitz.coeFn_compLp clamp_zero ((space U).starProjection v)
  rw [hp] at hae
  filter_upwards [hae] with x hx
  exact hx.symm ▸ clamp_range _
end EuclideanFiveColor.ContinuousVectors
end

noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace EuclideanFiveColor.ContinuousVectors
variable {A H : Type*} [AddCommGroup A] [TopologicalSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative A →* unitary (H →L[ℂ] H))
lemma covariance_mem (W : unitary (H →L[ℂ] H)) (φ : A ≃ₜ A) (hφ : φ 0 = 0)
    (hc : ∀ a v, (W : H →L[ℂ] H) (op U a v) = op U (φ a) ((W : H →L[ℂ] H) v))
    {v : H} (hv : v ∈ space U) : (W : H →L[ℂ] H) v ∈ space U := by
  have h0 : φ.symm 0 = 0 := by simpa only [hφ] using φ.symm_apply_apply 0
  have ht0 := φ.symm.continuous.tendsto 0
  rw [h0] at ht0
  have ht := ((W.val.continuous.tendsto v).comp hv).comp ht0
  change Tendsto (fun a => op U a ((W : H →L[ℂ] H) v)) (𝓝 0) (𝓝 ((W : H →L[ℂ] H) v))
  simpa only [Function.comp_def,hc,φ.apply_symm_apply] using ht
lemma projection_covariance_fixed (W : unitary (H →L[ℂ] H)) (φ : A ≃ₜ A) (hφ : φ 0 = 0)
    (hc : ∀ a v, (W : H →L[ℂ] H) (op U a v) = op U (φ a) ((W : H →L[ℂ] H) v))
    (v : H) (hv : (W : H →L[ℂ] H) v = v) :
    (W : H →L[ℂ] H) ((space U).starProjection v) = (space U).starProjection v := by
  exact projection_fixed_of_contraction (space U) (W : H →L[ℂ] H)
    (Unitary.linearIsometryEquiv W).lipschitz (fun w hw => covariance_mem U W φ hφ hc hw) v hv
lemma op_orthogonal (a : A) {v : H} (hv : v ∈ (space U)ᗮ) : op U a v ∈ (space U)ᗮ := by
  rw [Submodule.mem_orthogonal'] at hv ⊢
  intro w hw
  have hh := hv (op U (-a) w) (op_mem U (-a) hw)
  have he := Unitary.inner_map_map (U (Multiplicative.ofAdd a)) v (op U (-a) w)
  change ⟪op U a v,op U a (op U (-a) w)⟫_ℂ = _ at he
  rw [← op_add,add_neg_cancel,op_zero] at he
  exact he.trans hh
lemma projection_coefficient (v : H) (a : A)
    (hb : ⟪v-(space U).starProjection v, op U a (v-(space U).starProjection v)⟫_ℂ = 0) :
    ⟪(space U).starProjection v,op U a ((space U).starProjection v)⟫_ℂ = ⟪v,op U a v⟫_ℂ := by
  let p := (space U).starProjection v
  let b := v-p
  have hp : p ∈ space U := (space U).starProjection_apply_mem v
  have hbmem : b ∈ (space U)ᗮ := (space U).sub_starProjection_mem_orthogonal v
  have h1 : ⟪b,op U a p⟫_ℂ = 0 := (Submodule.mem_orthogonal' _ _).mp hbmem _ (op_mem U a hp)
  have h2 : ⟪p,op U a b⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp (op_orthogonal U a hbmem) _ hp
  have he : v = p+b := by dsimp [b]; abel
  change ⟪p,op U a p⟫_ℂ = ⟪v,op U a v⟫_ℂ
  rw [he,map_add,inner_add_left,inner_add_right,inner_add_right,h1,h2]
  change _ = _ + 0 + (0 + ⟪b,op U a b⟫_ℂ)
  rw [hb]; simp
end EuclideanFiveColor.ContinuousVectors
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Energy
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.Spectral.instCountableRot _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable

variable {Y : Type*} [MeasurableSpace Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] (q : D → Y)
variable (hq : Measurable q)
include hq in
lemma differenceFourier_projectedMass (z : E) :
    ∫ d, (eval z d : ℂ) ∂DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ) =
      (projectedMass μ q z : ℂ) := by
  let : IsProbabilityMeasure (μ.map q) :=
    (Measure.isProbabilityMeasure_map_iff hq.aemeasurable).mpr inferInstance
  rw [DifferenceFourier.difference_coefficient (eval z) (measurable_eval_coe z)]
  congr 1
  exact (norm_l2_sq (μ.map q) (conditional μ q (char z))).symm

variable [MulAction K Y] [MeasurableConstSMul K Y] [SMulInvariantMeasure K D μ]
variable (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
include hq hqcov in
lemma projectedMass_rotation (u : K) (z : E) :
    projectedMass μ q (kCoeff u*z) = projectedMass μ q z := by
  let : IsProbabilityMeasure (μ.map q) :=
    (Measure.isProbabilityMeasure_map_iff hq.aemeasurable).mpr inferInstance
  unfold projectedMass
  rw [← norm_project_l2 μ q hq, ← norm_project_l2 μ q hq]
  have hchar : char (kCoeff u*z) = act (mulRot u) (char z) := rfl
  rw [hchar]
  have he := (l2_eq_iff μ _ _).mpr (project_act μ q hq (fun g : Rot => hqcov (rotMul g)) (mulRot u) (char z))
  rw [he, l2_act]
  simp
include hq hqcov in
lemma projectedMass_radial {z w : E} (hn : ‖(z : ℂ)‖ = ‖(w : ℂ)‖) :
    projectedMass μ q z = projectedMass μ q w := by
  by_cases hw : w = 0
  · have hz : z = 0 := by
      apply Subtype.ext
      apply norm_eq_zero.mp
      simpa [hw] using hn
    rw [hz, hw]
  have hwc : (w : ℂ) ≠ 0 := fun h => hw (Subtype.ext h)
  let c : Circle := ⟨(z : ℂ)/(w : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div, hn, div_self (norm_ne_zero_iff.mpr hwc)])⟩
  let u : K := ⟨c, mem_algebraicClosure_iff.mp (div_mem z.property w.property)⟩
  have he : kCoeff u * w = z := by
    apply Subtype.ext
    exact div_mul_cancel₀ _ hwc
  rw [← he]
  exact projectedMass_rotation μ q hq hqcov u w
end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_RadialEnergy
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.Spectral.instCountableRot _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable

lemma norm_ofF (a : F) : ‖((ofF a : E) : ℂ)‖ = |(a : ℝ)| := by
  change ‖((a : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs]

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]
include hq hqcov in
omit [StandardBorelSpace Y] [Nonempty Y] [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)] in
lemma massReal_abs (a : F) : massReal μ q |a| = massReal μ q a := by
  apply projectedMass_radial μ q hq hqcov
  rw [norm_ofF, norm_ofF]
  change abs (abs (a : ℝ)) = abs (a : ℝ)
  exact abs_abs _
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable
variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]

include hq hqcov in
lemma massReal_vanish (hw : IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)))
    (r : F) (hr : 0 < r) : massReal μ q r = 0 := by
  haveI : IsProbabilityMeasure (μ.map q) := Measure.isProbabilityMeasure_map hq.aemeasurable
  by_contra hn
  obtain ⟨δ,hδ,ε,hε,hε1,hpos⟩ := radial_positive_near_zero μ q hq hqcov r hr hn
  let ν := DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)
  have he (t : F) : lineFourier ν 1 t = (massReal μ q t : ℂ) := by
    simpa only [ν,massReal,lineFourier_eq,one_mul] using differenceFourier_projectedMass μ q hq (ofF t)
  obtain ⟨t,ht,htδ,htε⟩ := exists_small_wild_parameter ({()} : Finset Unit) (by simp)
    ν hw (fun _ => (1:E)) (fun _ => one_ne_zero)
    (fun i t => by rw [he,Complex.ofReal_re]; exact projectedMass_nonneg μ q _)
    (show 0 < (δ:ℝ) from hδ) hε hε1
  have htest : massReal μ q t < ε := by
    have hh := htε () (by simp)
    rwa [he,Complex.ofReal_re] at hh
  have hgood := hpos |t| (abs_pos.mpr ht) (by exact_mod_cast htδ)
  rw [massReal_abs μ q hq hqcov] at hgood
  exact (not_lt_of_ge hgood) htest
end PlaneFiveColor.Spectral
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_SpectralMeasure
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace EuclideanFiveColor.BoundedMeasurable
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
lemma mulLpCLM_ae (f : Func X) (g : Lp ℂ 2 μ) :
    mulLpCLM μ f g =ᵐ[μ] fun x => f x * g x := mulLp_ae μ f g
lemma mulLp_l2 (f g : Func X) : mulLpCLM μ f (l2 μ g) = l2 μ (f*g) := by
  apply Lp.ext
  filter_upwards [mulLpCLM_ae μ f (l2 μ g),l2_ae μ g,l2_ae μ (f*g)] with x hx hy hz
  rw [hx,hy,hz]; rfl
end EuclideanFiveColor.BoundedMeasurable
end

noncomputable section
open scoped ComplexConjugate IsMulCommutative
namespace EuclideanFiveColor.CommutingSpectral
variable {G H : Type*} [CommGroup G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : G →* unitary (H →L[ℂ] H))
variable [TopologicalSpace G] [DiscreteTopology G]
lemma calculus_evaluation (g : G) : calculus U (evaluation g) = U g := by
  change ((gelfandStarTransform (algebra U)).symm ((evaluation g).comp ⟨character U,character_continuous U⟩) : H →L[ℂ] H) = U g
  have he : (evaluation g).comp ⟨character U,character_continuous U⟩ =
      gelfandStarTransform (algebra U) (generator U g) := by ext φ; rfl
  rw [he,StarAlgEquiv.symm_apply_apply]; rfl
end EuclideanFiveColor.CommutingSpectral
end

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
namespace EuclideanFiveColor.VectorMeasure
open BoundedMeasurable
variable {X H : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
omit [T2Space X] in
lemma boundedCM_toLp (μ : Measure X) [IsFiniteMeasure μ] (f : C(X,ℂ)) :
    l2 μ (boundedCM f) = ContinuousMap.toLp 2 μ ℂ f := by
  apply Lp.ext
  exact (l2_ae μ _).trans (ContinuousMap.coeFn_toLp (μ := μ) (p := 2) (𝕜 := ℂ) f).symm
lemma mulCM_toLp (f g : C(X,ℂ)) :
    mulLpCLM (measure Φ v) (boundedCM f) (ContinuousMap.toLp 2 (measure Φ v) ℂ g) =
      ContinuousMap.toLp 2 (measure Φ v) ℂ (f*g) := by
  rw [← boundedCM_toLp,← boundedCM_toLp,mulLp_l2]
  congr 1
lemma cyclicMap_mul (f : C(X,ℂ)) (g : Lp ℂ 2 (measure Φ v)) :
    cyclicMap Φ v (mulLpCLM (measure Φ v) (boundedCM f) g) = Φ f (cyclicMap Φ v g) := by
  refine (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)).induction
    (fun y hy => ?_) (isClosed_eq (by fun_prop) (by fun_prop)) g
  obtain ⟨h,rfl⟩ := hy
  rw [mulCM_toLp,cyclicMap_toLp,cyclicMap_toLp,map_mul]
  rfl
lemma cyclicMap_one : cyclicMap Φ v (l2 (measure Φ v) (1:Func X)) = v := by
  have he : (1:Func X) = boundedCM (1:C(X,ℂ)) := rfl
  rw [he,boundedCM_toLp,cyclicMap_toLp,map_one]
  rfl
lemma cyclicMap_inner (f g : Lp ℂ 2 (measure Φ v)) :
    ⟪cyclicMap Φ v f,cyclicMap Φ v g⟫_ℂ = ⟪f,g⟫_ℂ :=
  (cyclicIsometry Φ v).inner_map_map f g
lemma cyclicMap_pair_one (f : Func X) :
    ⟪v,cyclicMap Φ v (l2 (measure Φ v) f)⟫_ℂ = ∫ x, f x ∂measure Φ v := by
  nth_rw 1 [← cyclicMap_one Φ v]
  rw [cyclicMap_inner,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2_ae (measure Φ v) (1:Func X),l2_ae (measure Φ v) f] with x hx hy
  simp only [hx,hy,one_apply,RCLike.inner_apply,map_one,mul_one]
end EuclideanFiveColor.VectorMeasure
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.BoundedMeasurable
open EuclideanFiveColor.VectorMeasure EuclideanFiveColor.CommutingSpectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : DiscreteE →* unitary (H →L[ℂ] H)) (v : H)
lemma ordinaryIndicator_apply (d : D) : ordinaryIndicator d = (C:Set D).indicator (fun _ => (1:ℂ)) d := rfl
lemma ordinary_eval_continuous {d : D} (hd : d ∈ C) :
    Continuous (fun z : E => (eval z d : ℂ)) := by
  obtain ⟨ξ,rfl⟩ := hd
  change Continuous (fun z : E => (Circle.exp (inner ℝ (Multiplicative.toAdd ξ) (z:ℂ)) : ℂ))
  fun_prop
lemma ordinary_difference_tendsto (μ : Measure D) [IsFiniteMeasure μ] :
    Tendsto (fun z : E => ∫ d, ‖((eval z d : ℂ)-1)*ordinaryIndicator d‖^2 ∂μ)
      (𝓝 0) (𝓝 0) := by
  have hm (z : E) : Measurable (fun d => ‖((eval z d : ℂ)-1)*ordinaryIndicator d‖^2) := by
    have he : Measurable (fun d : D => (eval z d : ℂ)) := (evaluation (G := DiscreteE) (Multiplicative.ofAdd z)).continuous.measurable
    exact ((he.sub measurable_const).mul (measurable ordinaryIndicator)).norm.pow_const 2
  have hb (z : E) (d : D) : ‖‖((eval z d : ℂ)-1)*ordinaryIndicator d‖^2‖ ≤ (4:ℝ) := by
    have hi : ‖ordinaryIndicator d‖ ≤ 1 := by
      by_cases hd : d ∈ C <;> simp [ordinaryIndicator_apply,hd]
    have he : ‖(eval z d : ℂ)-1‖ ≤ 2 := by
      calc
        _ ≤ ‖(eval z d : ℂ)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [Circle.norm_coe, norm_one]; norm_num
    have hn : ‖((eval z d : ℂ)-1)*ordinaryIndicator d‖ ≤ 2 := by
      rw [norm_mul]
      exact (mul_le_mul he hi (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
    rw [Real.norm_eq_abs,abs_sq]
    nlinarith [norm_nonneg (((eval z d:ℂ)-1)*ordinaryIndicator d)]
  have hl (d : D) : Tendsto (fun z : E => ‖((eval z d : ℂ)-1)*ordinaryIndicator d‖^2)
      (𝓝 0) (𝓝 (0:ℝ)) := by
    by_cases hd : d ∈ C
    · have he := ((ordinary_eval_continuous hd).tendsto (0:E)).sub_const (1:ℂ)
      have ht := (he.mul_const (ordinaryIndicator d)).norm.pow 2
      have hz : (eval (0:E) d : ℂ) = 1 := by
        change (d 1 : ℂ) = 1
        rw [map_one]; rfl
      simpa only [hz,sub_self,zero_mul,norm_zero,zero_pow (by decide : 2 ≠ 0)] using ht
    · simp only [ordinaryIndicator_apply,Set.indicator_of_notMem hd,mul_zero,norm_zero,zero_pow (by decide : 2 ≠ 0)]
      exact tendsto_const_nhds
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ) (fun _ : D => (4:ℝ))
    (Filter.Eventually.of_forall (fun z : E => (hm z).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun z : E => Filter.Eventually.of_forall (hb z)))
    (integrable_const (4:ℝ)) (Filter.Eventually.of_forall hl)
  simpa only [integral_zero] using ht

lemma ordinaryVector_continuous : ordinaryVector U v ∈ ContinuousVectors.space U := by
  let μ := measure (calculus U) v
  have he (z : E) : ContinuousVectors.op U z (ordinaryVector U v) - ordinaryVector U v =
      cyclicMap (calculus U) v (l2 μ ((boundedCM (evaluation (G := DiscreteE) (Multiplicative.ofAdd z))-1)*ordinaryIndicator)) := by
    dsimp [ordinaryVector,μ]
    rw [sub_mul,map_sub,one_mul,map_sub]
    rw [← mulLp_l2,cyclicMap_mul]
    rw [calculus_evaluation U (Multiplicative.ofAdd z : DiscreteE)]
    rfl
  have hn (z : E) : ‖ContinuousVectors.op U z (ordinaryVector U v) - ordinaryVector U v‖^2 =
      ∫ d, ‖((eval z d:ℂ)-1)*ordinaryIndicator d‖^2 ∂μ := by
    rw [he]
    change ‖cyclicIsometry (calculus U) v _‖^2 = _
    rw [LinearIsometry.norm_map,norm_l2_sq]
    rfl
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.tendsto (0:ℝ) |>.comp (ordinary_difference_tendsto μ)
  simpa only [Function.comp_def,← hn,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using ht
lemma measure_ordinary_zero_of_orthogonal (hv : v ∈ (ContinuousVectors.space U)ᗮ) :
    measure (calculus U) v (C:Set D) = 0 := by
  have ho := (Submodule.mem_orthogonal' _ _).mp hv (ordinaryVector U v) (ordinaryVector_continuous U v)
  have hp := cyclicMap_pair_one (calculus U) v ordinaryIndicator
  change ⟪v,ordinaryVector U v⟫_ℂ = _ at hp
  rw [ho] at hp
  have hz : (measure (calculus U) v).real (C:Set D) = 0 := by
    have := congrArg Complex.re hp
    simpa only [ordinaryIndicator_apply,integral_indicator measurableSet_C,integral_const,
      Measure.restrict_apply_univ,Complex.real_smul, smul_eq_mul,mul_one,Complex.zero_re,Complex.ofReal_re,Measure.real] using this.symm
  exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top _ _)
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace EuclideanFiveColor.CommutingSpectral
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
lemma star_evaluation (g : G) : star (evaluation g) = evaluation g⁻¹ := by
  ext d
  change star (d g : ℂ) = (d g⁻¹ : ℂ)
  rw [map_inv]
  exact (Circle.coe_inv_eq_conj (d g)).symm
lemma evaluation_span_dense : Dense (Submodule.span ℂ (Set.range (evaluation (G := G))) : Set C(PontryaginDual G,ℂ)) := by
  let A := StarAlgebra.adjoin ℂ (Set.range (evaluation (G := G)))
  have hs : star (Set.range (evaluation (G := G))) = Set.range (evaluation (G := G)) := by
    ext f
    rw [Set.mem_star]
    constructor
    · rintro ⟨g,hg⟩
      refine ⟨g⁻¹,?_⟩
      rw [← star_evaluation,hg,star_star]
    · rintro ⟨g,rfl⟩
      exact ⟨g⁻¹,(star_evaluation g).symm⟩
  have he : A.toSubalgebra.toSubmodule = Submodule.span ℂ (Set.range (evaluation (G := G))) := by
    rw [StarAlgebra.adjoin_eq_span,hs,Set.union_self]
    have hc : Submonoid.closure (Set.range (evaluation (G := G))) = MonoidHom.mrange (evaluationHom (G := G)) :=
      Submonoid.closure_eq (MonoidHom.mrange (evaluationHom (G := G)))
    rw [hc]
    rfl
  have hsep : A.SeparatesPoints := by
    intro d e hde
    have hn : ∃ g, d g ≠ e g := by
      by_contra! h
      exact hde (DFunLike.ext _ _ h)
    obtain ⟨g,hg⟩ := hn
    refine ⟨evaluation g,⟨evaluation g,StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self g),rfl⟩,?_⟩
    change (d g : ℂ) ≠ (e g : ℂ)
    exact fun h => hg (Subtype.ext h)
  have ht := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  rw [dense_iff_closure_eq,← he]
  change closure (A:Set C(PontryaginDual G,ℂ)) = _
  rw [← StarSubalgebra.topologicalClosure_coe,ht]
  rfl
end EuclideanFiveColor.CommutingSpectral
namespace EuclideanFiveColor.CompactIntegral
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]
lemma apply_clm (f : C(X,ℂ)) : clm μ f = ∫ x, f x ∂μ := rfl
end EuclideanFiveColor.CompactIntegral
namespace EuclideanFiveColor.CommutingSpectral
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
lemma measure_eq_of_fourier (μ ν : Measure (PontryaginDual G)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.Regular] [ν.Regular]
    (h : ∀ g, ∫ d, (d g : ℂ) ∂μ = ∫ d, (d g : ℂ) ∂ν) : μ = ν := by
  have he : CompactIntegral.clm μ = CompactIntegral.clm ν := by
    apply ContinuousLinearMap.ext_on evaluation_span_dense
    rintro _ ⟨g,rfl⟩
    exact h g
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let fc : C(PontryaginDual G,ℂ) := ⟨fun d => (f d : ℂ),by fun_prop⟩
  have hh := congrArg (fun L : C(PontryaginDual G,ℂ) →L[ℂ] ℂ => (L fc).re) he
  simpa only [CompactIntegral.apply_clm,fc,ContinuousMap.coe_mk,integral_complex_ofReal,Complex.ofReal_re] using hh
end EuclideanFiveColor.CommutingSpectral
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Ergodicity
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable

lemma normF_pos {z : E} (hz : z ≠ 0) : 0 < normF z := by
  change 0 < ‖(z:ℂ)‖
  exact norm_pos_iff.mpr (fun h => hz (Subtype.ext h))

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]
include hq hqcov in
lemma projectedMass_vanish (hw : IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)))
    (z : E) (hz : z ≠ 0) : projectedMass μ q z = 0 := by
  have hn : ‖(z:ℂ)‖ = ‖((ofF (normF z):E):ℂ)‖ := by
    rw [norm_ofF,normF_coe,abs_of_nonneg (norm_nonneg _)]
  rw [projectedMass_radial μ q hq hqcov hn]
  exact massReal_vanish μ q hq hqcov hw (normF z) (normF_pos hz)
include hq hqcov in
lemma fourier_vanish_of_terminal (hw : IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)))
    (z : E) (hz : z ≠ 0) : ∫ d, (eval z d : ℂ) ∂μ = 0 := by
  have hn : ‖l2 μ (project μ q hq (char z))‖ = 0 := by
    rw [norm_project_l2]
    have he := projectedMass_vanish μ q hq hqcov hw z hz
    change ‖l2 (μ.map q) (conditional μ q (char z))‖^2 = 0 at he
    nlinarith [norm_nonneg (l2 (μ.map q) (conditional μ q (char z)))]
  have he : project μ q hq (char z) =ᵐ[μ] (0:Func D) :=
    (l2_eq_iff μ _ _).mp (by rw [map_zero]; exact norm_eq_zero.mp hn)
  change (∫ d, char z d ∂μ) = 0
  rw [← project_integral μ q hq]
  calc
    _ = ∫ d, (0:Func D) d ∂μ := integral_congr_ae he
    _ = 0 := by simp

lemma ergodic_wild_fourier (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
    (hw : IsWild μ) (z : E) (hz : z ≠ 0) : ∫ d, (eval z d : ℂ) ∂μ = 0 := by
  obtain ⟨q,hq,hqc,hgood,hmix⟩ := exists_terminal_factor μ
  have := hmix
  have hd : IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)) := by
    refine ⟨relative_difference_invariant μ id q measurable_id hq (fun k => Eventually.of_forall (fun d => rfl)) hqc,?_⟩
    exact hgood id measurable_id (fun k => Eventually.of_forall (fun d => rfl)) (by simpa using hw)
  exact fourier_vanish_of_terminal μ q hq hqc hd z hz
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.Amenable.Mean
variable {G H : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
lemma vector_mem_closedConvexHull (M : Amenable.Mean G) (V : G →ᵇ H) :
    M.vector V ∈ closedConvexHull ℝ (Set.range V) := by
  by_contra hn
  obtain ⟨L,c,hL,hc⟩ := geometric_hahn_banach_closed_point convex_closedConvexHull isClosed_closedConvexHull hn
  have he : L (M.vector V) = M.map (L.compLeftContinuousBounded G V) := by
    rw [← M.vector_map]
    apply ext_inner_right ℝ
    intro x
    simp only [M.vector_pair, RCLike.inner_apply, conj_trivial]
    change M.map (pairing (L.compLeftContinuousBounded G V) x) = x * M.map (L.compLeftContinuousBounded G V)
    have hp : pairing (L.compLeftContinuousBounded G V) x = x • L.compLeftContinuousBounded G V := by
      ext g; simp [pairing_apply]
    rw [hp,map_smul]; rfl
  have hb : M.map (L.compLeftContinuousBounded G V) ≤ c := by
    rw [← M.map_const c]
    apply M.mono
    intro g
    exact le_of_lt (hL _ (subset_closedConvexHull (𝕜 := ℝ) (Set.mem_range_self g)))
  linarith
end EuclideanFiveColor.Amenable.Mean
namespace EuclideanFiveColor
namespace ConvexAverage
variable {G H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
lemma norm_le (A : ConvexAverage G) (f : G → H) {C : ℝ} (hf : ∀ g, ‖f g‖ ≤ C) : ‖A.apply f‖ ≤ C := by
  calc
    _ ≤ ∑ i, ‖A.weight i • f (A.pt i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, A.weight i * C := Finset.sum_le_sum fun i _ => by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (A.nonneg i)]
      exact mul_le_mul_of_nonneg_left (hf _) (A.nonneg i)
    _ = C := by rw [← Finset.sum_mul,A.total,one_mul]
lemma of_mem_convexHull {f : G → H} {v : H} (hv : v ∈ convexHull ℝ (Set.range f)) :
    ∃ A : ConvexAverage G, A.apply f = v := by
  classical
  obtain ⟨ι,hi,w,z,hw,ht,hz,he⟩ := mem_convexHull_iff_exists_fintype.mp hv
  choose g hg using hz
  let e := (Fintype.equivFin ι).symm
  refine ⟨⟨Fintype.card ι,g ∘ e,w ∘ e,fun i => hw _,?_⟩,?_⟩
  · simpa only [Function.comp_apply] using (e.sum_comp w).trans ht
  · dsimp [apply]
    simp only [hg]
    exact (e.sum_comp (fun i => w i • z i)).trans he
end ConvexAverage
namespace Amenable.Mean
variable {G H : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
lemma exists_finite_approx (M : Mean G) (V : G →ᵇ H) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ConvexAverage G, ‖A.apply V - M.vector V‖ < ε := by
  have h := M.vector_mem_closedConvexHull V
  rw [closedConvexHull_eq_closure_convexHull] at h
  obtain ⟨v,hv,he⟩ := Metric.mem_closure_iff.mp h ε hε
  obtain ⟨A,rfl⟩ := ConvexAverage.of_mem_convexHull hv
  exact ⟨A,by simpa [dist_eq_norm,norm_sub_rev] using (show dist (M.vector V) (A.apply V) < ε from he)⟩
end Amenable.Mean
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor
namespace ConvexAverage
open BoundedMeasurable
variable {G X : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]
lemma bm_apply (A : ConvexAverage G) (f : Func X) (x : X) : A.bm f x = A.apply (fun g => f (g +ᵥ x)) := by
  simp [bm,apply,Func,Finset.sum_apply]
lemma bm_bound (A : ConvexAverage G) (f : Func X) (x : X) : ‖A.bm f x‖ ≤ bound f := by
  rw [bm_apply]; exact A.norm_le _ (fun g => norm_le_bound f _)
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma l2_bm (A : ConvexAverage G) (f : Func X) :
    l2 μ (A.bm f) = A.apply (fun g => Amenable.Koopman.action μ g (l2 μ f)) := by
  simp only [bm,apply,map_sum,map_smul,l2_act]
end ConvexAverage
namespace InvariantSequence
open BoundedMeasurable
variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (M : Amenable.Mean G)
lemma limit_measurable (f : Func X) : Measurable (limit μ M f : X → ℂ) := (Lp.stronglyMeasurable _).measurable
lemma limit_fixed (f : Func X) (g : G) :
    (fun x => limit μ M f (g +ᵥ x)) =ᵐ[μ] (limit μ M f : X → ℂ) := by
  have h := M.vector_orbit_invariant (Amenable.Koopman.action μ) (Amenable.Koopman.action_add μ) (l2 μ f) g
  exact (Amenable.Koopman.coe_action μ g _).symm.trans (by rw [show Amenable.Koopman.action μ g (limit μ M f) = limit μ M f from h])
lemma exists_averages (f : Func X) : ∃ A : ℕ → ConvexAverage G,
    ∀ᵐ x ∂μ, Tendsto (fun n => A n |>.bm f x) atTop (𝓝 (limit μ M f x)) := by
  classical
  let V := Amenable.Mean.orbit (Amenable.Koopman.action (G := G) μ) (l2 μ f)
  choose A hA using (fun n : ℕ => M.exists_finite_approx V (show (0:ℝ) < 1/(n+1:ℝ) by positivity))
  have ht : Tendsto (fun n => l2 μ ((A n).bm f)) atTop (𝓝 (limit μ M f)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt ?_) (tendsto_one_div_add_atTop_nhds_zero_nat)
    simpa only [ConvexAverage.l2_bm, ConvexAverage.apply, V, limit, Amenable.Mean.orbit_apply] using hA n
  have hm := (tendstoInMeasure_of_tendsto_Lp ht).congr_left (fun n => l2_ae μ ((A n).bm f))
  obtain ⟨r,_,hr⟩ := hm.exists_seq_tendsto_ae
  exact ⟨fun n => A (r n),hr⟩
end InvariantSequence
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace EuclideanFiveColor
open BoundedMeasurable
namespace ConvexAverage
variable {G X : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma setIntegral_bm (A : ConvexAverage G) (f : Func X) (s : Set X) (hs : MeasurableSet s)
    (hinv : ∀ g : G, (fun x => g +ᵥ x) ⁻¹' s =ᵐ[μ] s) :
    ∫ x in s, A.bm f x ∂μ = ∫ x in s, f x ∂μ := by
  have hpres (g : G) : MeasurePreserving (fun x : X => g +ᵥ x) (μ.restrict s) (μ.restrict s) := by
    convert (measurePreserving_vadd g μ).restrict_preimage hs using 1
    all_goals try with_reducible_and_instances rfl
    exact (Measure.restrict_congr_set (hinv g)).symm
  simp only [bm_apply,apply]
  rw [integral_finsetSum _ (fun i _ => by
    have hh : Integrable (fun x => f (A.pt i +ᵥ x)) μ := integrable μ (act (A.pt i) f)
    exact hh.restrict.smul (A.weight i))]
  simp only [integral_smul]
  have he (i : Fin A.n) : ∫ x in s, f (A.pt i +ᵥ x) ∂μ = ∫ x in s, f x ∂μ :=
    (hpres _).integral_comp (MeasurableEquiv.vadd _).measurableEmbedding _
  simp only [he,← Finset.sum_smul,A.total,one_smul]
lemma setIntegral_of_limit (f : Func X) (A : ℕ → ConvexAverage G) (c : ℂ)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun n => (A n).bm f x) atTop (𝓝 c))
    (s : Set X) (hs : MeasurableSet s)
    (hinv : ∀ g : G, (fun x => g +ᵥ x) ⁻¹' s =ᵐ[μ] s) :
    ∫ x in s, f x ∂μ = μ.real s • c := by
  have ht := tendsto_integral_of_dominated_convergence (fun _ : X => (bound f : ℝ))
    (fun n => (measurable ((A n).bm f)).aestronglyMeasurable)
    (integrable_const (bound f : ℝ) : Integrable (fun _ : X => (bound f : ℝ)) (μ.restrict s))
    (fun n => Eventually.of_forall (fun x => (A n).bm_bound f x)) (ae_restrict_of_ae hc)
  simp only [setIntegral_bm μ _ _ s hs hinv,integral_const,Measure.real,Measure.restrict_apply_univ] at ht
  exact tendsto_nhds_unique tendsto_const_nhds ht
end ConvexAverage
namespace ErgodicCriterion
variable (X : Type*) [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
lemma testSet_union (s t : Finset ℕ) : testSet X (s ∪ t) = testSet X s ∩ testSet X t := by
  ext x; simp [testSet]; aesop
lemma pi_testSet : IsPiSystem (Set.range (testSet X)) := by
  rintro a ⟨s,rfl⟩ b ⟨t,rfl⟩ _
  exact ⟨s ∪ t,testSet_union X s t⟩
lemma generate_testSet : MeasurableSpace.generateFrom (Set.range (testSet X)) = ‹MeasurableSpace X› := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨s,rfl⟩; exact measurable_testSet X s
  · conv_lhs => rw [← MeasurableSpace.generateFrom_natGeneratingSequence X]
    apply MeasurableSpace.generateFrom_mono
    rintro _ ⟨n,rfl⟩
    exact ⟨{n},by simp [testSet]⟩
lemma test_apply (s : Finset ℕ) (x : X) : test X s x = (testSet X s).indicator (fun _ => (1:ℂ)) x := rfl
variable {X}
variable {G : Type*} [AddCommGroup G] [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma ergodic_of_test_limits (A : Finset ℕ → ℕ → ConvexAverage G) (c : Finset ℕ → ℂ)
    (hA : ∀ i, ∀ᵐ x ∂μ, Tendsto (fun n => (A i n).bm (test X i) x) atTop (𝓝 (c i))) :
    ErgodicVAdd G X μ := by
  refine ⟨fun {s} hs hinv => ?_⟩
  have hall (i : Finset ℕ) : ∫ x, test X i x ∂μ = c i := by
    simpa using ConvexAverage.setIntegral_of_limit μ (test X i) (A i) (c i) (hA i)
      Set.univ MeasurableSet.univ (fun _ => Eventually.of_forall (fun _ => rfl))
  have htest (i : Finset ℕ) : (μ.restrict s).real (testSet X i) = μ.real s * μ.real (testSet X i) := by
    have he := ConvexAverage.setIntegral_of_limit μ (test X i) (A i) (c i) (hA i) s hs hinv
    rw [← hall i] at he
    simp only [test_apply] at he
    rw [integral_indicator_const _ (measurable_testSet X i),
      integral_indicator_const _ (measurable_testSet X i)] at he
    simpa using congrArg Complex.re he
  have he : μ.restrict s = μ s • μ := by
    apply ext_of_generate_finite (Set.range (testSet X)) (generate_testSet X).symm (pi_testSet X)
    · rintro _ ⟨i,rfl⟩
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by simp; finiteness)).mp
      simpa [Measure.real,Measure.smul_apply,ENNReal.toReal_mul] using htest i
    · simp
  have hr : μ.real s = μ.real s * μ.real s := by
    have hh := congrArg (fun ν : Measure X => ν.real s) he
    simpa [Measure.real,Measure.restrict_apply hs,Set.inter_self] using hh
  have hz : μ.real s = 0 ∨ μ.real s = 1 := by
    have hh : μ.real s * (μ.real s-1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hh with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [eventuallyConst_set]
  rcases hz with h | h
  · right
    rw [ae_iff]
    simpa using (show μ s = 0 by rw [← ofReal_measureReal]; simp [h])
  · left
    apply (ae_iff_measure_eq hs.nullMeasurableSet).mpr
    change μ s = μ Set.univ
    rw [← ofReal_measureReal (μ := μ) (s := s)]
    simp [h]
end ErgodicCriterion
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace EuclideanFiveColor.InvariantDecomposition
open BoundedMeasurable ErgodicCriterion
variable {G X : Type*} [AddCommGroup G] [Countable G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (M : Amenable.Mean G)
omit [Countable G] [Nonempty X] in
lemma code_measurable : Measurable (code μ M) :=
  Measurable.of_eval (fun i => InvariantSequence.limit_measurable μ M (test X i))
omit [Countable G] [Nonempty X] in
lemma code_fixed (g : G) : (fun x => code μ M (g +ᵥ x)) =ᵐ[μ] code μ M := by
  have h := (ae_all_iff.mpr (fun i => InvariantSequence.limit_fixed μ M (test X i) g))
  exact h.mono fun x hx => funext hx
lemma fiber_invariant : ∀ᵐ y ∂μ.map (code μ M), VAddInvariantMeasure G X (condDistrib id (code μ M) μ y) := by
  have h (g : G) : ∀ᵐ y ∂μ.map (code μ M),
      (condDistrib id (code μ M) μ y).map (fun x => g +ᵥ x) = condDistrib id (code μ M) μ y := by
    have h := KernelSupport.condDistrib_equivariant μ id (code μ M) measurable_id (code_measurable μ M)
      (MeasurableEquiv.vadd g) (MeasurableEquiv.refl _) (fun x => g +ᵥ x)
      (measurable_const_vadd g) (measurePreserving_vadd g μ) (code_fixed μ M g)
      (Eventually.of_forall (fun _ => rfl))
    exact h.mono fun _ hy => hy.symm
  filter_upwards [ae_all_iff.mpr h] with y hy
  constructor
  intro g s hs
  rw [← Measure.map_apply (measurable_const_vadd _) hs,hy]
lemma fiber_ergodic : ∀ᵐ y ∂μ.map (code μ M), ErgodicVAdd G X (condDistrib id (code μ M) μ y) := by
  choose A hA using (fun i => InvariantSequence.exists_averages μ M (test X i))
  have hc := ConditionalFiber.ae_fiber_of_ae μ (code μ M) (code_measurable μ M) (ae_all_iff.mpr hA)
  filter_upwards [fiber_invariant μ M,hc, ConditionalFiber.ae_in_own_fiber μ (code μ M) (code_measurable μ M)] with y hy hlim hcode
  let := hy
  apply ergodic_of_test_limits (condDistrib id (code μ M) μ y) A y
  intro i
  filter_upwards [hlim,hcode] with x hx he
  have hh := hx i
  change Tendsto _ atTop (𝓝 (code μ M x i)) at hh
  rwa [he] at hh
end EuclideanFiveColor.InvariantDecomposition
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open EuclideanFiveColor
namespace PlaneFiveColor.Spectral
lemma smul_ergodic_of_rot (μ : Measure D) [ErgodicVAdd Rot D μ] : ErgodicSMul K D μ := by
  have : SMulInvariantMeasure K D μ := ⟨fun k s hs => measure_preimage_vadd μ (mulRot k) s⟩
  constructor
  intro s hs hi
  apply ErgodicVAdd.aeconst_of_forall_preimage_vadd_ae_eq (G := Rot) hs
  exact fun g => hi (rotMul g)
/-- The arbitrary invariant wild case, obtained from actual conditional ergodic fibers. -/
lemma wild_fourier (μ : Measure D) [IsProbabilityMeasure μ]
    (hw : IsWild μ) (z : E) (hz : z ≠ 0) : ∫ d, (eval z d : ℂ) ∂μ = 0 := by
  have : SMulInvariantMeasure K D μ := ⟨fun k s hs => (hw.1 k).measure_preimage hs.nullMeasurableSet⟩
  let M : Amenable.Mean Rot := MovingMean.toMean (fun _ => 0)
  let q := InvariantDecomposition.code μ M
  have hq : Measurable q := InvariantDecomposition.code_measurable μ M
  have hc : ∀ᵐ d ∂μ, d ∉ (C : Set D) := by
    rw [ae_iff]
    simpa using hw.2
  have hf := ConditionalFiber.ae_fiber_of_ae μ q hq hc
  have he : ∀ᵐ y ∂μ.map q, ∫ d, (eval z d : ℂ) ∂condDistrib id q μ y = 0 := by
    filter_upwards [InvariantDecomposition.fiber_ergodic μ M, hf] with y hy hC
    let := hy
    have := smul_ergodic_of_rot (condDistrib id q μ y)
    apply ergodic_wild_fourier (condDistrib id q μ y) ?_ z hz
    refine ⟨fun k => measurePreserving_smul k _,?_⟩
    rw [ae_iff] at hC
    simpa using hC
  rw [← ConditionalFiber.integral_fiber μ q hq (fun d => (eval z d : ℂ))
    (BoundedMeasurable.integrable μ (char z))]
  exact integral_eq_zero_of_ae he
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.VectorMeasure EuclideanFiveColor.CommutingSpectral
lemma finite_wild_fourier (μ : Measure D) [IsFiniteMeasure μ] (hw : IsWild μ)
    (z : E) (hz : z ≠ 0) : ∫ d, (eval z d:ℂ) ∂μ = 0 := by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hu : μ Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hμ
  let ν := (μ Set.univ)⁻¹ • μ
  have : IsProbabilityMeasure ν := ⟨by
    rw [Measure.smul_apply,smul_eq_mul,ENNReal.inv_mul_cancel hu (measure_ne_top μ Set.univ)]⟩
  have hwν : IsWild ν := ⟨fun k => (hw.1 k).smul_measure _,by simp [ν,Measure.smul_apply,hw.2]⟩
  have hh := wild_fourier ν hwν z hz
  rw [integral_smul_measure] at hh
  exact (smul_eq_zero.mp hh).resolve_left (by
    rw [ENNReal.toReal_inv]
    exact inv_ne_zero ((ENNReal.toReal_pos hu (measure_ne_top μ Set.univ)).ne'))
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : DiscreteE →* unitary (H →L[ℂ] H)) (W : K → unitary (H →L[ℂ] H))
  (hcov : ∀ k z w, (W k : H →L[ℂ] H) (ContinuousVectors.op U z w) =
    ContinuousVectors.op U ((kCoeff k)*z) ((W k : H →L[ℂ] H) w))
include hcov
lemma vectorMeasure_invariant (v : H) (hfix : ∀ k, (W k : H →L[ℂ] H) v = v) :
    ∀ k : K, MeasurePreserving (fun d : D => k • d) (measure (calculus U) v) (measure (calculus U) v) := by
  intro k
  have hm : Measurable (fun d : D => k • d) := (continuous_scalar (kCoeff k)).measurable
  refine ⟨hm,measure_eq_of_fourier _ _ (fun z => ?_)⟩
  change (∫ d, evaluation z d ∂(measure (calculus U) v).map (fun d : D => k • d)) = _
  rw [integral_map hm.aemeasurable ((evaluation z).continuous.measurable.aestronglyMeasurable)]
  change (∫ d, (eval (kCoeff k * Multiplicative.toAdd z) d : ℂ) ∂measure (calculus U) v) = _
  have hc (a : E) : (∫ d, (eval a d:ℂ) ∂measure (calculus U) v) =
      ⟪v,ContinuousVectors.op U a v⟫_ℂ := by
    have hh := integral_complex (calculus U) v (evaluation (G := DiscreteE) (Multiplicative.ofAdd a))
    rw [calculus_evaluation U (Multiplicative.ofAdd a : DiscreteE)] at hh
    exact hh
  change (∫ d, (eval (kCoeff k * Multiplicative.toAdd z) d : ℂ) ∂measure (calculus U) v) =
    ∫ d, (eval (Multiplicative.toAdd z) d:ℂ) ∂measure (calculus U) v
  rw [hc,hc]
  calc
    _ = ⟪(W k : H →L[ℂ] H) v,ContinuousVectors.op U (kCoeff k * Multiplicative.toAdd z) ((W k : H →L[ℂ] H) v)⟫_ℂ := by rw [hfix k]
    _ = ⟪(W k : H →L[ℂ] H) v,(W k : H →L[ℂ] H) (ContinuousVectors.op U (Multiplicative.toAdd z) v)⟫_ℂ := by rw [hcov]
    _ = _ := Unitary.inner_map_map (W k) v (ContinuousVectors.op U (Multiplicative.toAdd z) v)
lemma residual_fourier (v : H) (hv : v ∈ (ContinuousVectors.space U)ᗮ)
    (hfix : ∀ k, (W k : H →L[ℂ] H) v = v) (z : E) (hz : z ≠ 0) :
    ⟪v,ContinuousVectors.op U z v⟫_ℂ = 0 := by
  have hw : IsWild (measure (calculus U) v) :=
    ⟨vectorMeasure_invariant U W hcov v hfix,measure_ordinary_zero_of_orthogonal U v hv⟩
  have hh := finite_wild_fourier (measure (calculus U) v) hw z hz
  have hc := integral_complex (calculus U) v (evaluation (G := DiscreteE) (Multiplicative.ofAdd z))
  rw [calculus_evaluation U (Multiplicative.ofAdd z : DiscreteE)] at hc
  exact hc.symm.trans hh
end PlaneFiveColor.Spectral
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_BorelTransfer
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
namespace PlaneFiveColor.LabelModel
open Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
variable (k : ℕ) (ω : Space k)
lemma color_ae (i : Fin k) : colorVector k ω i =ᵐ[measure k ω] colorValue k i := (color_memLp k ω i).coeFn_toLp
lemma color_rotation_fixed (i : Fin k) (b : K) :
    (rotation k ω b : Hilbert k ω →L[ℂ] Hilbert k ω) (colorVector k ω i) = colorVector k ω i := by
  rw [rotation_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (colorVector k ω i) (rotate_preserving k ω b),
    (rotate_preserving k ω b).quasiMeasurePreserving.ae (color_ae k ω i),color_ae k ω i] with η h1 h2 h3
  simp only [Function.comp_apply,h1,h2,h3,colorValue,rotate_apply,mul_zero]
lemma color_unit_correlation (i : Fin k) (b : K) :
    ⟪colorVector k ω i,op (representation k ω) (kCoeff b) (colorVector k ω i)⟫_ℂ = 0 := by
  rw [op_apply,L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [color_ae k ω i,Lp.coeFn_compMeasurePreserving (colorVector k ω i) (trans_preserving k ω (kCoeff b)),
    (trans_preserving k ω (kCoeff b)).quasiMeasurePreserving.ae (color_ae k ω i)] with η h1 h2 h3
  simp only [h1,h2,Function.comp_apply,h3,colorValue,trans_apply,zero_add]
  have hp : η.val 0 ≠ η.val (kCoeff b) := η.property 0 (kCoeff b) (by
    change ‖(0 : ℂ)-(b.val:ℂ)‖ = 1
    rw [zero_sub,norm_neg]
    exact Circle.norm_coe b.val)
  by_cases hi : η.val 0 = i
  · have hj : η.val (kCoeff b) ≠ i := fun h => hp (hi.trans h.symm)
    simp [hi,hj]
  · simp [hi]
lemma projected_range (i : Fin k) : ∀ᵐ η ∂measure k ω,
    ((projected k ω i) η).im = 0 ∧ 0 ≤ ((projected k ω i) η).re ∧ ((projected k ω i) η).re ≤ 1 := by
  apply projection_range (measure k ω) (representation k ω) (trans k) (trans_preserving k ω) (op_apply k ω)
  filter_upwards [color_ae k ω i] with η h
  rw [h]
  dsimp [colorValue]
  split_ifs <;> norm_num
lemma projected_rotation_fixed (i : Fin k) (b : K) :
    (rotation k ω b : Hilbert k ω →L[ℂ] Hilbert k ω) (projected k ω i) = projected k ω i := by
  exact projection_covariance_fixed (representation k ω) (rotation k ω b)
    (Homeomorph.mulLeft₀ (kCoeff b) (kCoeff_ne_zero b)) (mul_zero _)
    (rotation_covariance k ω b) _ (color_rotation_fixed k ω i b)
lemma projected_unit_correlation (i : Fin k) (b : K) :
    ⟪projected k ω i,op (representation k ω) (kCoeff b) (projected k ω i)⟫_ℂ = 0 := by
  have hb := residual_fourier (representation k ω) (rotation k ω) (rotation_covariance k ω)
    (colorVector k ω i-projected k ω i)
    ((space (A := E) (representation k ω)).sub_starProjection_mem_orthogonal (colorVector k ω i))
    (fun b => by rw [map_sub,color_rotation_fixed,projected_rotation_fixed]) (kCoeff b) (kCoeff_ne_zero b)
  exact (projection_coefficient (representation k ω) (colorVector k ω i) (kCoeff b) hb).trans (color_unit_correlation k ω i b)
end PlaneFiveColor.LabelModel
end

noncomputable section
open MeasureTheory Filter Topology
namespace PlaneFiveColor.LabelModel
open Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
variable (k : ℕ) (ω : Space k)
lemma one_ae : oneVector k ω =ᵐ[measure k ω] fun _ => (1 : ℂ) := MemLp.coeFn_toLp _
lemma one_fixed (a : E) : op (representation k ω) a (oneVector k ω) = oneVector k ω := by
  rw [op_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (oneVector k ω) (trans_preserving k ω a),
    (trans_preserving k ω a).quasiMeasurePreserving.ae (one_ae k ω),one_ae k ω] with η h1 h2 h3
  exact h1.trans (h2.trans h3.symm)
lemma one_continuous : oneVector k ω ∈ space (A := E) (representation k ω) := by
  change Tendsto (fun a : E => op (representation k ω) a (oneVector k ω)) (𝓝 0) (𝓝 (oneVector k ω))
  simpa only [one_fixed] using (tendsto_const_nhds : Tendsto (fun _ : E => oneVector k ω) (𝓝 0) (𝓝 (oneVector k ω)))
lemma color_sum : ∑ i : Fin k, colorVector k ω i = oneVector k ω := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.univ) (colorVector k ω),ae_all_iff.mpr (color_ae k ω),one_ae k ω] with η h1 h2 h3
  rw [h1,h3]
  simp_rw [h2,colorValue]
  simp
lemma projected_sum : ∑ i : Fin k, projected k ω i = oneVector k ω := by
  change ∑ i : Fin k, (space (A := E) (representation k ω)).starProjection (colorVector k ω i) = _
  rw [← map_sum,color_sum]
  exact (space (A := E) (representation k ω)).starProjection_eq_self_iff.mpr (one_continuous k ω)
end PlaneFiveColor.LabelModel
end

noncomputable section
open Filter Topology
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral
lemma algebraic_norm (z : E) : IsAlgebraic ℚ (‖(z:ℂ)‖ : ℂ) := by
  have hz : IsAlgebraic ℚ (z : ℂ) := mem_algebraicClosure_iff.mp z.property
  have hc : IsAlgebraic ℚ (conj (z : ℂ)) := hz.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom
  apply IsAlgebraic.of_pow (n := 2) (by norm_num)
  simpa only [Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_pow] using hz.mul hc
end PlaneFiveColor.Spectral
end

noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.ContinuousVectors
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : DiscreteE →* unitary (H →L[ℂ] H))
lemma orbit_uniformContinuous {v : H} (hv : v ∈ space (A := E) U) : UniformContinuous (fun a : E => op U a v) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,h⟩ := Metric.continuousAt_iff.mp (orbit_continuous U hv).continuousAt ε hε
  refine ⟨δ,hδ,fun a b hab => ?_⟩
  have ht : dist (op U (a-b) v) v < ε := by
    have hh := h (show dist (a-b) 0 < δ by simpa only [dist_zero_right,dist_eq_norm,sub_zero] using hab)
    simpa only [op_zero (A := E) U] using hh
  calc
    _ = dist (op U b (op U (a-b) v)) (op U b v) := by
      rw [← op_add (A := E) U]
      congr 2
      abel_nf
    _ = dist (op U (a-b) v) v := dist_op U b _ _
    _ < ε := ht
lemma orbitExtension_continuous {v : H} (hv : v ∈ space (A := E) U) : Continuous (orbitExtension U v) :=
  (dense_E.uniformContinuous_extend (orbit_uniformContinuous U hv)).continuous
lemma orbitExtension_eq {v : H} (hv : v ∈ space (A := E) U) (a : E) : orbitExtension U v (a : ℂ) = op U a v :=
  dense_E.extend_eq (orbit_continuous U hv) a
lemma orbitExtension_inner {v w : H} (hv : v ∈ space (A := E) U) (hw : w ∈ space (A := E) U) (x y : ℂ) :
    ⟪orbitExtension U v x,orbitExtension U w (x+y)⟫_ℂ = ⟪v,orbitExtension U w y⟫_ℂ := by
  have hc := orbitExtension_continuous U hv
  have hd := orbitExtension_continuous U hw
  refine dense_E.denseRange_val.induction_on₂
    (p := fun x y : ℂ => ⟪orbitExtension U v x,orbitExtension U w (x+y)⟫_ℂ = ⟪v,orbitExtension U w y⟫_ℂ) ?_ ?_ x y
  · exact isClosed_eq ((hc.comp continuous_fst).inner (hd.comp (continuous_fst.add continuous_snd)))
      (continuous_const.inner (hd.comp continuous_snd))
  · intro a b
    change ⟪orbitExtension U v (a : ℂ),orbitExtension U w ((a+b : E) : ℂ)⟫_ℂ = _
    rw [orbitExtension_eq U hv,orbitExtension_eq U hw,orbitExtension_eq U hw,op_add (A := E) U]
    exact Unitary.inner_map_map (U (Multiplicative.ofAdd a)) v (op U b w)
end PlaneFiveColor.Spectral
end

noncomputable section
open Filter Topology
namespace PlaneFiveColor.Spectral
lemma normalized_algebraic (z : E) (hz : z ≠ 0) :
    ∃ b : K, (b.val : ℂ) = (z : ℂ) / (‖(z:ℂ)‖ : ℂ) := by
  have hn : ‖(z:ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (Subtype.coe_ne_coe.mpr hz)
  have hb : ‖(z:ℂ) / (‖(z:ℂ)‖ : ℂ)‖ = 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_self hn]
  have hzalg : IsAlgebraic ℚ (z : ℂ) := mem_algebraicClosure_iff.mp z.property
  exact ⟨⟨⟨_,mem_sphere_zero_iff_norm.mpr hb⟩,
    by
      change IsAlgebraic ℚ ((z : ℂ)/(‖(z:ℂ)‖ : ℂ))
      simpa only [div_eq_mul_inv] using hzalg.mul (algebraic_norm z).inv⟩,rfl⟩
lemma circle_closed_induction {p : ℂ → Prop} (hp : IsClosed {z | p z})
    (halg : ∀ b : K, p (b.val : ℂ)) (u : Circle) : p (u : ℂ) := by
  obtain ⟨s,hs,ht⟩ := mem_closure_iff_seq_limit.mp (dense_E (u : ℂ))
  have hne : ∀ᶠ n in atTop, s n ≠ 0 := ht.eventually (isOpen_compl_singleton.mem_nhds (Circle.coe_ne_zero u))
  have hnorm : Tendsto (fun n => s n / (‖s n‖ : ℂ)) atTop (𝓝 (u : ℂ)) := by
    have h := ht.div (Complex.continuous_ofReal.continuousAt.tendsto.comp ht.norm)
      (show (‖(u:ℂ)‖ : ℂ) ≠ 0 by simp [Circle.norm_coe])
    have he : (u : ℂ) / (‖(u:ℂ)‖ : ℂ) = (u : ℂ) := by simp only [Circle.norm_coe,Complex.ofReal_one,div_one]
    rw [he] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  apply hp.mem_of_tendsto hnorm
  filter_upwards [hne] with n hn
  obtain ⟨b,hb⟩ := normalized_algebraic ⟨s n,hs n⟩ (fun h => hn (congrArg Subtype.val h))
  rw [← hb]
  exact halg b
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace
namespace PlaneFiveColor.LabelModel
open Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
variable (k : ℕ) (ω : Space k)
lemma projected_continuous (i : Fin k) : projected k ω i ∈ space (A := E) (representation k ω) :=
  (space (A := E) (representation k ω)).starProjection_apply_mem _
lemma fieldVector_continuous (i : Fin k) : Continuous (fieldVector k ω i) :=
  orbitExtension_continuous _ (projected_continuous k ω i)
lemma fieldVector_algebraic (i : Fin k) (a : E) : fieldVector k ω i (a : ℂ) = op (representation k ω) a (projected k ω i) :=
  orbitExtension_eq _ (projected_continuous k ω i) a
lemma fieldVector_sum (x : ℂ) : ∑ i : Fin k, fieldVector k ω i x = oneVector k ω := by
  refine dense_E.denseRange_val.induction_on x (isClosed_eq (continuous_finsetSum _ (fun i _ => fieldVector_continuous k ω i)) continuous_const) ?_
  intro a
  simp only [fieldVector_algebraic,← map_sum,projected_sum,one_fixed]
lemma fieldVector_range (i : Fin k) (x : ℂ) : ∀ᵐ η ∂measure k ω,
    (fieldVector k ω i x η).im = 0 ∧ 0 ≤ (fieldVector k ω i x η).re ∧ (fieldVector k ω i x η).re ≤ 1 := by
  have he : clamp_lipschitz.compLp clamp_zero (fieldVector k ω i x) = fieldVector k ω i x := by
    refine dense_E.denseRange_val.induction_on x (isClosed_eq
      ((clamp_lipschitz.continuous_compLp clamp_zero).comp (fieldVector_continuous k ω i)) (fieldVector_continuous k ω i)) ?_
    intro a
    rw [fieldVector_algebraic,op_apply]
    apply Lp.ext
    filter_upwards [clamp_lipschitz.coeFn_compLp clamp_zero (Lp.compMeasurePreserving (trans k a) (trans_preserving k ω a) (projected k ω i)),
      Lp.coeFn_compMeasurePreserving (projected k ω i) (trans_preserving k ω a),
      (trans_preserving k ω a).quasiMeasurePreserving.ae (projected_range k ω i)] with η h1 h2 h3
    simp only [Function.comp_apply] at h1 h2
    rw [h1,h2]
    exact clamp_eq h3
  have ha := clamp_lipschitz.coeFn_compLp clamp_zero (fieldVector k ω i x)
  rw [he] at ha
  filter_upwards [ha] with η hη
  exact hη.symm ▸ clamp_range _
lemma fieldVector_unit_correlation (i : Fin k) (x : ℂ) (u : Circle) :
    ⟪fieldVector k ω i x,fieldVector k ω i (x+u)⟫_ℂ = 0 := by
  rw [show ⟪fieldVector k ω i x,fieldVector k ω i (x+u)⟫_ℂ =
    ⟪projected k ω i,fieldVector k ω i u⟫_ℂ from
    orbitExtension_inner _ (projected_continuous k ω i) (projected_continuous k ω i) x u]
  apply circle_closed_induction (isClosed_eq (continuous_const.inner (fieldVector_continuous k ω i)) continuous_const) _ u
  intro b
  change ⟪projected k ω i,fieldVector k ω i ((kCoeff b : E) : ℂ)⟫_ℂ = 0
  rw [fieldVector_algebraic]
  exact projected_unit_correlation k ω i b
end PlaneFiveColor.LabelModel
end

noncomputable section
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal
namespace EuclideanFiveColor
variable {T X : Type*} [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
  [MeasurableSpace T] [BorelSpace T] [MeasurableSpace X] (μ : Measure X)
  (f : T → Lp ℂ 2 μ) (hf : Continuous f)
include hf
lemma index_measurable (n : ℕ) : Measurable (approxIndex μ f hf n) := by
  apply measurable_find
  intro j
  exact isOpen_lt (continuous_const.dist hf) continuous_const |>.measurableSet
omit [MeasurableSpace T] [BorelSpace T] in
lemma index_bound (n : ℕ) (t : T) :
    dist (f (TopologicalSpace.denseSeq T (approxIndex μ f hf n t))) (f t) < (1/2:ℝ)^n := by
  unfold approxIndex
  exact Nat.find_spec (dense_approx μ f hf t ((1/2:ℝ)^n) (by positivity))
lemma approxField_measurable (n : ℕ) : Measurable (approxField μ f hf n) := by
  have h : Measurable (fun p : ℕ × X => f (TopologicalSpace.denseSeq T p.1) p.2) :=
    measurable_from_prod_countable_right fun j => (Lp.stronglyMeasurable (f (TopologicalSpace.denseSeq T j))).measurable
  exact h.comp (((index_measurable μ f hf n).comp measurable_fst).prodMk measurable_snd)
omit [MeasurableSpace T] [BorelSpace T] in
lemma approxField_tendsto (t : T) : ∀ᵐ x ∂μ,
    Tendsto (fun n => approxField μ f hf n (t,x)) atTop (𝓝 (f t x)) := by
  let g : ℕ → Lp ℂ 2 μ := fun n => f (TopologicalSpace.denseSeq T (approxIndex μ f hf n t))-f t
  have hs : Summable (fun n => ‖g n‖) := summable_geometric_two.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by simpa only [g,dist_eq_norm] using (index_bound μ f hf n t).le)
  have ha : ∀ᵐ x ∂μ, Summable (fun n => ‖g n x‖) := by
    apply summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1:ℝ≥0∞) ≤ 2) (fun n => Lp.aestronglyMeasurable (g n))
    simpa only [← Lp.enorm_def] using (tsum_enorm_ne_top_iff_summable_norm.mpr hs)
  have he : ∀ᵐ x ∂μ, ∀ n, g n x = approxField μ f hf n (t,x)-f t x :=
    ae_all_iff.mpr fun n => Lp.coeFn_sub _ _
  filter_upwards [ha,he] with x hx he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [he] using hx.tendsto_atTop_zero
lemma measurableField_measurable : Measurable (measurableField μ f hf) := by
  have hr := Measurable.limsup fun n => Complex.continuous_re.measurable.comp (approxField_measurable μ f hf n)
  have hi := Measurable.limsup fun n => Complex.continuous_im.measurable.comp (approxField_measurable μ f hf n)
  have hh := (Complex.continuous_ofReal.measurable.comp hr).add ((Complex.continuous_ofReal.measurable.comp hi).mul_const Complex.I)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  apply Complex.ext <;> simp [measurableField]
lemma exists_measurable_field : ∃ F : T × X → ℂ, Measurable F ∧ ∀ t, (fun x => F (t,x)) =ᵐ[μ] f t := by
  refine ⟨measurableField μ f hf,?_,?_⟩
  · exact measurableField_measurable μ f hf
  · intro t
    filter_upwards [approxField_tendsto μ f hf t] with x hx
    apply Complex.ext
    · exact (Complex.continuous_re.continuousAt.tendsto.comp hx).limsup_eq
    · exact (Complex.continuous_im.continuousAt.tendsto.comp hx).limsup_eq
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace EuclideanFiveColor
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
lemma positive_orthogonal (v w : Lp ℂ 2 μ)
    (hv : ∀ᵐ x ∂μ, (v x).im = 0 ∧ 0 ≤ (v x).re)
    (hw : ∀ᵐ x ∂μ, (w x).im = 0 ∧ 0 ≤ (w x).re)
    (ho : ⟪v,w⟫_ℂ = 0) : ∀ᵐ x ∂μ, (v x).re * (w x).re = 0 := by
  have hi := L2.integrable_inner (𝕜 := ℂ) v w
  have he : (fun x => (⟪v x,w x⟫_ℂ).re) =ᵐ[μ] (fun x => (v x).re * (w x).re) := by
    filter_upwards [hv,hw] with x hx hy
    simp [RCLike.inner_apply,Complex.mul_re,hx.1,hy.1,mul_comm]
  have hh : Integrable (fun x => (v x).re * (w x).re) μ := hi.re.congr he
  apply (integral_eq_zero_iff_of_nonneg_ae _ hh).mp
  · rw [← integral_congr_ae he]
    change (∫ x, RCLike.re (⟪v x,w x⟫_ℂ) ∂μ) = 0
    rw [integral_re hi,← L2.inner_def,ho]
    rfl
  · filter_upwards [hv,hw] with x hx hy
    exact mul_nonneg hx.2 hy.2
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace PlaneFiveColor.LabelModel
open Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
variable (k : ℕ) (ω : Space k)
lemma exists_label_field : ∃ H : Fin k → ℂ × Space k → ℝ,
    (∀ i, Measurable (H i)) ∧
    (∀ x : ℂ, ∀ᵐ η ∂measure k ω, ∑ i, H i (x,η) = 1) ∧
    (∀ x : ℂ, ∀ u : Circle, ∀ᵐ η ∂measure k ω, ∀ i, H i (x,η)*H i (x+u,η) = 0) := by
  have hex (i : Fin k) := exists_measurable_field (measure k ω) (fieldVector k ω i) (fieldVector_continuous k ω i)
  choose F hm hae using hex
  refine ⟨fun i p => (F i p).re,fun i => Complex.continuous_re.measurable.comp (hm i),?_,?_⟩
  · intro x
    have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin k => fieldVector k ω i x)
    rw [fieldVector_sum] at hs
    filter_upwards [ae_all_iff.mpr (fun i => hae i x),hs,one_ae k ω] with η he hs h1
    have hc : ∑ i : Fin k, F i (x,η) = 1 := by
      simp_rw [he]
      exact hs.symm.trans h1
    have hr := congrArg Complex.re hc
    simpa only [map_sum,Complex.re_sum,Complex.one_re] using hr
  · intro x u
    apply ae_all_iff.mpr
    intro i
    have hz := positive_orthogonal (measure k ω) (fieldVector k ω i x) (fieldVector k ω i (x+u))
      ((fieldVector_range k ω i x).mono fun _ h => ⟨h.1,h.2.1⟩)
      ((fieldVector_range k ω i (x+u)).mono fun _ h => ⟨h.1,h.2.1⟩)
      (fieldVector_unit_correlation k ω i x u)
    filter_upwards [hae i x,hae i (x+u),hz] with η h1 h2 h3
    simpa only [h1,h2] using h3
end PlaneFiveColor.LabelModel
end

noncomputable section
open MeasureTheory
namespace EuclideanFiveColor
variable {X : Type*} [MeasurableSpace X] {k : ℕ} [NeZero k]
omit [NeZero k] in
lemma positiveSupport_measurable (f : Fin k → X → ℝ) (hf : ∀ i, Measurable (f i)) : Measurable (positiveSupport f) := by
  apply measurable_finset_iff.mpr
  intro i
  simp only [positiveSupport,Finset.mem_filter,Finset.mem_univ,true_and]
  exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const (hf i))
lemma positiveSelect_measurable (f : Fin k → X → ℝ) (hf : ∀ i, Measurable (f i)) : Measurable (positiveSelect f) :=
  (measurable_of_countable pickSupport).comp (positiveSupport_measurable f hf)
omit [MeasurableSpace X] in
lemma positiveSelect_pos (f : Fin k → X → ℝ) (x : X) (hs : ∑ i, f i x = 1) : 0 < f (positiveSelect f x) x := by
  have hex : ∃ i, 0 < f i x := by
    by_contra! h
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    linarith
  have hn : (positiveSupport f x).Nonempty := by
    obtain ⟨i,hi⟩ := hex
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  have hmem : positiveSelect f x ∈ positiveSupport f x := by
    simp only [positiveSelect,pickSupport,dite_eq_left hn]
    exact hn.choose_spec
  exact (Finset.mem_filter.mp hmem).2
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter
namespace EuclideanFiveColor
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure S) [SFinite ν]
  (d : S → ℂ) (hd : Measurable d) {k : ℕ} [NeZero k]
include hd
lemma sample_field (H : Fin k → ℂ × Ω → ℝ) (hm : ∀ i, Measurable (H i))
    (hp : ∀ x : ℂ, ∀ᵐ ω ∂μ, ∑ i, H i (x,ω) = 1)
    (ho : ∀ x : ℂ, ∀ s : S, ∀ᵐ ω ∂μ, ∀ i, H i (x,ω)*H i (x+d s,ω) = 0) :
    ∃ c : ℂ → Fin k, Measurable c ∧ ∀ᵐ p ∂(volume : Measure ℂ).prod ν, c p.1 ≠ c (p.1+d p.2) := by
  let c : ℂ × Ω → Fin k := positiveSelect H
  have hc : Measurable c := positiveSelect_measurable H hm
  have ha (p : ℂ × S) : ∀ᵐ ω ∂μ, c (p.1,ω) ≠ c (p.1+d p.2,ω) := by
    filter_upwards [hp p.1,hp (p.1+d p.2),ho p.1 p.2] with ω h1 h2 h3
    intro he
    have hpos1 := positiveSelect_pos H (p.1,ω) h1
    have hpos2 := positiveSelect_pos H (p.1+d p.2,ω) h2
    change 0 < H (c (p.1,ω)) (p.1,ω) at hpos1
    change 0 < H (c (p.1+d p.2,ω)) (p.1+d p.2,ω) at hpos2
    rw [← he] at hpos2
    exact (mul_pos hpos1 hpos2).ne' (h3 _)
  have hm1 : Measurable (fun q : (ℂ × S) × Ω => c (q.1.1,q.2)) :=
    hc.comp ((measurable_fst.fst).prodMk measurable_snd)
  have hm2 : Measurable (fun q : (ℂ × S) × Ω => c (q.1.1+d q.1.2,q.2)) :=
    hc.comp (((measurable_fst.fst).add (hd.comp measurable_fst.snd)).prodMk measurable_snd)
  have hh : ∀ᵐ ω ∂μ, ∀ᵐ p ∂(volume : Measure ℂ).prod ν, c (p.1,ω) ≠ c (p.1+d p.2,ω) :=
    (Measure.ae_ae_comm (measurableSet_eq_fun hm1 hm2).compl).mp (.of_forall ha)
  obtain ⟨ω,hω⟩ := hh.exists
  exact ⟨fun x => c (x,ω),hc.comp (measurable_id.prodMk measurable_const),hω⟩
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory
namespace EuclideanFiveColor
lemma proper_to_borel_weak_oai {k : ℕ} [NeZero k] {c : ℂ → Fin k} (hc : ProperColoring k c) :
    ∃ d : ℂ → Fin k, Measurable d ∧ WeakColoring k d := by
  let ω : PlaneFiveColor.LabelModel.Space k := ⟨fun x => c x,fun x y h => hc x y h⟩
  obtain ⟨H,hm,hp,ho⟩ := PlaneFiveColor.LabelModel.exists_label_field k ω
  obtain ⟨d,hd,hunit⟩ := sample_field (PlaneFiveColor.LabelModel.measure k ω) angularMeasure
    direction direction_continuous.measurable
    H hm hp (fun x t => ho x (AddCircle.toCircle t))
  exact ⟨d,hd,hd.aemeasurable,hunit⟩
end EuclideanFiveColor
end

end OAI
end

theorem solution : type_of% @OAI.EuclideanFiveColor.proper_to_borel_weak_oai := @OAI.EuclideanFiveColor.proper_to_borel_weak_oai
