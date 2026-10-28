-- Prove2me | solution 1 for OAI.BorsukNine.Admissible.regularPatch_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:02:36.653313+00:00
-- url     : https://prove2.me/submissions/ce7b17ca-5842-44c8-8380-719cb74fa813

import Mathlib
import Definitions.Def_OAIQ058B000

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_MatrixNorm
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section MatrixNorm
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν

lemma matrix_action_norm_sq (A : Matrix ν ν ℝ) (x : E) :
    ‖(Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) A x‖ ^ 2 =
      ⟪x, (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) (star A * A) x⟫ := by
  rw [map_mul, map_star]
  change ‖(Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) A x‖ ^ 2 =
    ⟪x, (star ((Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) A)) ((Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) A x)⟫
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]

lemma sqrt_action_norm_sq (Q : Matrix ν ν ℝ) (hQ : 0 ≤ Q) (x : E) :
    ‖(Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) (CFC.sqrt Q) x‖ ^ 2 = ⟪x, (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) Q x⟫ := by
  rw [matrix_action_norm_sq, (CFC.sqrt_nonneg Q).star_eq, CFC.sqrt_mul_sqrt_self Q hQ]

end MatrixNorm

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_SignedExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SignedExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]

omit [Nonempty ν] in
lemma matrix_posPart_continuousOn :
    ContinuousOn (fun A : Matrix ν ν ℝ => A⁺) {A | IsSelfAdjoint A} := by
  have hc : Continuous (fun A : Matrix ν ν ℝ => (1 / 2 : ℝ) • (CFC.abs A + A)) :=
    (continuous_const (y := (1 / 2 : ℝ))).smul (CFC.continuous_abs.add continuous_id)
  apply hc.continuousOn.congr
  intro A hA
  change A⁺ = (1 / 2 : ℝ) • (CFC.abs A + A)
  rw [CFC.abs_add_self A hA, two_smul, smul_add]
  module

end SignedExtension

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_SpectralSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section SpectralSupport
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν

omit [DecidableEq ν] [Nonempty ν] in

lemma subspace_eq_span_of_inner_separates (W : Submodule ℝ E) (w u : E)
    (hu : u ∈ W) (huw : ⟪w,u⟫ ≠ 0)
    (hsep : ∀ v ∈ W, ⟪w,v⟫ = 0 → v = 0) : W = Submodule.span ℝ {u} := by
  apply le_antisymm
  · intro v hv
    have hz : v - (⟪w,v⟫ / ⟪w,u⟫) • u = 0 := hsep _
      (W.sub_mem hv (W.smul_mem _ hu)) (by rw [inner_sub_right,inner_smul_right]; field_simp; ring)
    rw [sub_eq_zero] at hz
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  · exact Submodule.span_le.mpr (by simpa using hu)

end SpectralSupport
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_RankPreimage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section RankOnePreimage
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Nonempty ν] in
lemma symmetric_inner_action {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) (u v : E) :
    ⟪u,op A v⟫ = ⟪op A u,v⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.star_eq_adjoint,
    ← map_star,hA.star_eq]

omit [Nonempty ν] in
lemma symmetric_eq_rankOne_of_range {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A)
    {u : E} (hu : ‖u‖ = 1)
    (hR : LinearMap.range (op A).toLinearMap ≤ Submodule.span ℝ {u}) :
    A = ⟪u,op A u⟫ • rankOne u := by
  have he (v : E) : op A v = ⟪u,op A v⟫ • u := by
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp (hR (LinearMap.mem_range_self _ v))
    change t • u = (op A) v at ht
    rw [← ht,inner_smul_right,real_inner_self_eq_norm_sq,hu,one_pow,mul_one]
  have hscalar (v : E) : ⟪u,op A v⟫ = ⟪u,op A u⟫ * ⟪u,v⟫ := by
    calc
      ⟪u,op A v⟫ = ⟪op A u,v⟫ := symmetric_inner_action hA u v
      _ = ⟪u,op A u⟫ * ⟪u,v⟫ := by
        conv_lhs => rw [he u]
        simp only [inner_smul_left,conj_trivial]
  apply (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).injective
  change op A = op (⟪u,op A u⟫ • rankOne u)
  rw [map_smul]
  apply ContinuousLinearMap.ext
  intro v
  rw [smul_apply,rankOne_action,smul_smul,← hscalar,← he]

end RankOnePreimage
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_SpectralChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
section SpectralChart
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Nonempty ν] in
lemma positiveProjection_action {A : M} (hA : IsSelfAdjoint A) (hU : IsUnit A)
    {v : E} (hv : v ∈ LinearMap.range (op A⁺).toLinearMap) :
    op (positiveProjection A) v = v := by
  obtain ⟨x,rfl⟩ := hv
  have hAP : A * A⁺ = A⁺ * A⁺ := by
    calc
      A * A⁺ = (A⁺ - A⁻) * A⁺ := by rw [CFC.posPart_sub_negPart A hA]
      _ = A⁺ * A⁺ := by rw [sub_mul,CFC.negPart_mul_posPart,sub_zero]
  have he : positiveProjection A * A⁺ = A⁺ := by
    dsimp [positiveProjection]
    rw [mul_assoc,← hAP,← mul_assoc,Ring.inverse_mul_cancel A hU,one_mul]
  have hh := congrArg (fun B : M => op B x) he
  simpa only [map_mul,mul_apply_eq_comp,ContinuousLinearMap.coe_coe] using hh

omit [Nonempty ν] in
lemma positiveProjection_kills {A : M} {u v : E} {lam : ℝ}
    (hP : A⁺ = lam • rankOne u) (hv : ⟪u,v⟫ = 0) :
    op (positiveProjection A) v = 0 := by
  simp only [positiveProjection,map_mul,mul_apply_eq_comp,hP,map_smul,
    smul_apply,rankOne_action,hv,zero_smul,map_zero,smul_zero]

omit [Nonempty ν] in
lemma positiveRange_separated_of_close {A B : M} (hB : IsSelfAdjoint B)
    (hBU : IsUnit B) {u : E} {lam : ℝ} (hP : A⁺ = lam • rankOne u)
    (hclose : ‖op (positiveProjection B) - op (positiveProjection A)‖ < 1)
    {v : E} (hv : v ∈ LinearMap.range (op B⁺).toLinearMap) (horth : ⟪u,v⟫ = 0) : v = 0 := by
  have he : (op (positiveProjection B) - op (positiveProjection A)) v = v := by
    rw [sub_apply,positiveProjection_action hB hBU hv,
      positiveProjection_kills hP horth,sub_zero]
  have hn := ContinuousLinearMap.le_opNorm (op (positiveProjection B) - op (positiveProjection A)) v
  rw [he] at hn
  apply norm_eq_zero.mp
  have hp := norm_nonneg v
  nlinarith

omit [Nonempty ν] in
lemma positive_eq_rankOne_of_separated {A : M} {w : E}
    (hAw : op A⁺ w ≠ 0)
    (hsep : ∀ v ∈ LinearMap.range (op A⁺).toLinearMap, ⟪w,v⟫ = 0 → v = 0) :
    ∃ u : E, ‖u‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ A⁺ = lam • rankOne u := by
  let v : E := op A⁺ w
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,norm_inv,hAw,v]
  have hur : u ∈ LinearMap.range (op A⁺).toLinearMap :=
    Submodule.smul_mem _ _ (LinearMap.mem_range_self _ w)
  have hwu : ⟪w,u⟫ ≠ 0 := by
    intro hz
    have hu0 := hsep u hur hz
    simp [hu0] at hu
  have hr := subspace_eq_span_of_inner_separates
    (LinearMap.range (op A⁺).toLinearMap) w u hur hwu hsep
  have he := symmetric_eq_rankOne_of_range (CFC.posPart_nonneg A).isSelfAdjoint hu hr.le
  have hl : 0 ≤ ⟪u,op A⁺ u⟫ := by
    rw [← sqrt_action_norm_sq A⁺ (CFC.posPart_nonneg A) u]
    positivity
  have hl0 : ⟪u,op A⁺ u⟫ ≠ 0 := by
    intro hz
    have hP0 : A⁺ = 0 := by simpa only [hz,zero_smul] using he
    apply hAw
    simp [hP0]
  exact ⟨u,hu,_,lt_of_le_of_ne hl (Ne.symm hl0),he⟩

omit [Nonempty ν] in
lemma positiveProjection_continuousAt {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x))
    {x : X} (hU : IsUnit (A x)) : ContinuousAt (positiveProjection ∘ A) x := by
  have hP : Continuous (fun x => (A x)⁺) :=
    (matrix_posPart_continuousOn.comp_continuous hA (fun y => hSA y))
  have hInv : ContinuousAt (fun y => Ring.inverse (A y)) x := by
    obtain ⟨a,ha⟩ := hU
    have hi := NormedRing.inverse_continuousAt a
    rw [ha] at hi
    exact hi.comp hA.continuousAt
  exact hInv.mul hP.continuousAt

omit [Nonempty ν] in
lemma positive_line_eventually {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x))
    {x : X} (hU : IsUnit (A x)) {w : E} (hw : ‖w‖ = 1)
    {lam : ℝ} (hlam : 0 < lam) (hP : (A x)⁺ = lam • rankOne w) :
    ∀ᶠ y in 𝓝 x, IsUnit (A y) ∧ ∃ u : E, ‖u‖ = 1 ∧
      ∃ t : ℝ, 0 < t ∧ (A y)⁺ = t • rankOne u := by
  have hop : Continuous (fun B : M => op B) :=
    (op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hQ := hop.continuousAt.comp (positiveProjection_continuousAt A hA hSA hU)
  have hclose : ∀ᶠ y in 𝓝 x, ‖op (positiveProjection (A y)) - op (positiveProjection (A x))‖ < 1 := by
    have ht := (hQ.sub (continuousAt_const (y := op (positiveProjection (A x))))).norm
    exact ht.eventually_lt continuousAt_const (by simp)
  have hPcont : Continuous (fun y => (A y)⁺) :=
    matrix_posPart_continuousOn.comp_continuous hA (fun y => hSA y)
  have hvcont : Continuous (fun y => op (A y)⁺ w) := (hop.comp hPcont).clm_apply continuous_const
  have hw0 : op (A x)⁺ w ≠ 0 := by
    rw [hP,map_smul,smul_apply,rankOne_action,real_inner_self_eq_norm_sq,hw]
    have hwne : w ≠ 0 := by intro he; simp only [he,norm_zero] at hw; norm_num at hw
    simpa only [one_pow,one_smul] using smul_ne_zero (ne_of_gt hlam) hwne
  have hv : ∀ᶠ y in 𝓝 x, op (A y)⁺ w ≠ 0 := hvcont.continuousAt.eventually_ne hw0
  have hunit : ∀ᶠ y in 𝓝 x, IsUnit (A y) :=
    hA.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hU)
  filter_upwards [hclose,hv,hunit] with y hy hyv hyU
  refine ⟨hyU,positive_eq_rankOne_of_separated hyv ?_⟩
  exact fun v hv he => positiveRange_separated_of_close (hSA y) hyU hP hy hv he

end SpectralChart
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_LineRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
section LineRepresentative
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Nonempty ν] in
lemma lineRepresentative_continuousOn {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) (w : E) :
    ContinuousOn (fun x => lineRepresentative w (A x)) {x | op (A x)⁺ w ≠ 0} := by
  have hop : Continuous (fun B : M => op B) :=
    (op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hP : Continuous (fun x => (A x)⁺) :=
    matrix_posPart_continuousOn.comp_continuous hA hSA
  have hv : Continuous (fun x => op (A x)⁺ w) := (hop.comp hP).clm_apply continuous_const
  exact (hv.norm.continuousOn.inv₀ (fun _ hx => norm_ne_zero_iff.mpr hx)).smul hv.continuousOn

omit [Nonempty ν] in
lemma positive_line_isOpen {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) :
    IsOpen {x | IsUnit (A x) ∧ HasPositiveLine (A x)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨u,hu,lam,hl,he⟩ := hx.2
  exact positive_line_eventually A hA hSA hx.1 hu hl he

end LineRepresentative
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_HemisphereChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
open SimplicialChains
section HemisphereChart
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
variable (w : E) (e : W →ₗᵢ[ℝ] E)

lemma hemisphereInverse_continuousOn :
    ContinuousOn (hemisphereInverse w e) {u | 0 < ⟪w,u⟫} :=
  ((continuous_const.inner continuous_id).continuousOn.inv₀ (fun _ h => ne_of_gt h)).smul
    e.toContinuousLinearMap.adjoint.continuous.continuousOn
end HemisphereChart
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_NegativeQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace Topology
open Filter Set
section NegativeQuadratic
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
omit [FiniteDimensional ℝ E] in
lemma negativeQuadratic_of_unit (B : E →L[ℝ] E)
    (h : ∀ v, ‖v‖ = 1 → ⟪v,B v⟫ < 0) : NegativeQuadratic B := by
  intro v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hh := h (‖v‖⁻¹ • v) (by simp [norm_smul,norm_inv,hv])
  rw [map_smul,real_inner_smul_left,real_inner_smul_right] at hh
  by_contra hge
  exact not_lt_of_ge (mul_nonneg (inv_nonneg.mpr hn.le)
    (mul_nonneg (inv_nonneg.mpr hn.le) (le_of_not_gt hge))) hh
lemma negativeQuadratic_isOpen (B : X → E →L[ℝ] E) (hB : Continuous B) :
    IsOpen {x | NegativeQuadratic (B x)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hcont : Continuous (fun p : X × E => ⟪p.2,B p.1 p.2⟫) :=
    continuous_snd.inner ((hB.comp continuous_fst).clm_apply continuous_snd)
  have hev := (isCompact_sphere (0:E) 1).eventually_forall_of_forall_eventually
    (P := fun y v => ⟪v,B y v⟫ < 0) (x₀ := x) (fun v hv =>
      hcont.continuousAt.eventually_lt continuousAt_const
        (hx v (fun he => by simp [he] at hv)))
  filter_upwards [hev] with y hy
  exact negativeQuadratic_of_unit (B y) (fun v hv => hy v (by simpa using hv))
end NegativeQuadratic
end BorsukNine

namespace BorsukNine
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixBlocks
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ

lemma blockScalar_continuous (c : E) : Continuous (blockScalar c : M → ℝ) :=
  continuous_const.inner (((Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).clm_apply continuous_const)
end MatrixBlocks
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_LocalParity_RegularPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set

section RegularPatchContinuity
variable {domainIndices rangeIndices labels : Type*}
  [Fintype domainIndices] [Fintype rangeIndices] [Fintype labels]
  [DecidableEq domainIndices] [DecidableEq rangeIndices]
local notation "E" => EuclideanSpace ℝ rangeIndices
local notation "W" => EuclideanSpace ℝ domainIndices
local notation "op" => Matrix.toEuclideanCLM (n := rangeIndices) (𝕜 := ℝ)

private lemma regularPatch_negative_isOpen (frame : W →ₗᵢ[ℝ] E) :
    IsOpen {point : traceSphere rangeIndices |
      NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress frame point.val))} := by
  have hoperator : Continuous (fun matrix : Matrix domainIndices domainIndices ℝ =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) matrix) :=
    (Matrix.toEuclideanCLM (n := domainIndices) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact negativeQuadratic_isOpen _
    (hoperator.comp ((matrixCompress frame).continuous_of_finiteDimensional.comp continuous_subtype_val))

omit [DecidableEq domainIndices] [DecidableEq rangeIndices] in
private lemma regularPatch_target_isOpen {f : E → labels → ℝ} (hf : Admissible f)
    (indices : Finset labels) (center : E) (frame : W →ₗᵢ[ℝ] E) (radius : ℝ) :
    IsOpen ({vector : E | ∀ index ∈ indices, 0 < f vector index} ∩
      ({vector : E | 0 < ⟪center,vector⟫} ∩
        (fun vector => ‖hemisphereInverse center frame vector‖) ⁻¹' Iio radius)) := by
  have hpos : IsOpen {vector : E | ∀ index ∈ indices, 0 < f vector index} := by
    have he : {vector : E | ∀ index ∈ indices, 0 < f vector index} =
        ⋂ index ∈ indices, {vector : E | 0 < f vector index} := by ext vector; simp
    rw [he]
    exact isOpen_biInter_finset (fun index _ => isOpen_lt continuous_const (hf.smooth index).continuous)
  have hinner : IsOpen {vector : E | 0 < ⟪center,vector⟫} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  exact hpos.inter ((hemisphereInverse_continuousOn center frame).norm.isOpen_inter_preimage
    hinner (isOpen_Iio : IsOpen (Iio radius)))

private lemma regularPatch_representative_isOpen (vector : E) {target : Set E}
    (htarget : IsOpen target) :
    IsOpen {point : traceSphere rangeIndices | op point.val⁺ vector ≠ 0 ∧
      lineRepresentative vector point.val ∈ target} := by
  have hval : Continuous (fun point : traceSphere rangeIndices => point.val) :=
    continuous_subtype_val
  have hself : ∀ point : traceSphere rangeIndices, IsSelfAdjoint point.val :=
    fun point => point.property.1
  have hmatrix : Continuous (fun matrix : Matrix rangeIndices rangeIndices ℝ => op matrix) :=
    (op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hpositive : Continuous (fun point : traceSphere rangeIndices => point.val⁺) :=
    matrix_posPart_continuousOn.comp_continuous hval hself
  have hoperator : Continuous (fun point : traceSphere rangeIndices => op point.val⁺ vector) :=
    (hmatrix.comp hpositive).clm_apply continuous_const
  exact (lineRepresentative_continuousOn _ hval hself vector).isOpen_inter_preimage
    (isClosed_eq hoperator continuous_const).isOpen_compl htarget

private lemma regularPatch_isOpen_aux {f : E → labels → ℝ} (hf : Admissible f)
    (I : Finset labels) (w c : E) (e : W →ₗᵢ[ℝ] E) (δ : ℝ) :
    IsOpen {A : traceSphere rangeIndices |
      IsUnit A.val ∧ HasPositiveLine A.val ∧ op A.val⁺ w ≠ 0 ∧
      (∀ i ∈ I, 0 < f (lineRepresentative w A.val) i) ∧
      0 < ⟪c,lineRepresentative w A.val⟫ ∧
      ‖hemisphereInverse c e (lineRepresentative w A.val)‖ < δ ∧
      0 < blockScalar c A.val ∧
      NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A.val))} := by
  let T := traceSphere rangeIndices
  have hA : Continuous (fun A : T => A.val) := continuous_subtype_val
  have hSA : ∀ A : T, IsSelfAdjoint A.val := fun A => A.property.1
  have hpre := regularPatch_representative_isOpen w (regularPatch_target_isOpen hf I c e δ)
  have hscalar : IsOpen {A : T | 0 < blockScalar c A.val} :=
    isOpen_lt continuous_const ((blockScalar_continuous c).comp hA)
  have hneg := regularPatch_negative_isOpen e
  apply isOpen_iff_mem_nhds.mpr
  rintro point ⟨hunit,hline,hvector,hlabels,hinner,hnorm,hblock,hquadratic⟩
  filter_upwards [(positive_line_isOpen _ hA hSA).mem_nhds ⟨hunit,hline⟩,
    hpre.mem_nhds ⟨hvector,hlabels,hinner,hnorm⟩,
    hscalar.mem_nhds hblock, hneg.mem_nhds hquadratic]
    with nearby hpositive hrepresentative hscalar hnegative
  exact ⟨hpositive.1,hpositive.2,hrepresentative.1,hrepresentative.2.1,
    hrepresentative.2.2.1,hrepresentative.2.2.2,hscalar,hnegative⟩
end RegularPatchContinuity

section RegularPatch
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)

omit [DecidableEq ι] in
lemma Admissible.regularPatch_isOpen_oai {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) (w c : E) (e : W →ₗᵢ[ℝ] E) (δ : ℝ) : IsOpen (regularPatch f I w c e δ) :=
  regularPatch_isOpen_aux hf I w c e δ
end RegularPatch
end BorsukNine

end OAI
end

theorem solution.{u_1} : type_of% @OAI.BorsukNine.Admissible.regularPatch_isOpen_oai.{u_1} := @OAI.BorsukNine.Admissible.regularPatch_isOpen_oai.{u_1}
