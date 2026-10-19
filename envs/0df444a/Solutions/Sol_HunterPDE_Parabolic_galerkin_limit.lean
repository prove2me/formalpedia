-- Prove2me | solution 1 for HunterPDE.Parabolic.galerkin_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T05:24:36.562036+00:00
-- url     : https://prove2.me/submissions/bd8a233f-5630-4a40-8e8f-4e9744b93d25

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10
import Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Parabolic_WeakSolution
import Definitions.Def_HunterPDE_Parabolic_HilbertTriple
import Theorems.Thm_HunterPDE_Parabolic_galerkin_energy_estimate
import Theorems.Thm_HunterPDE_Parabolic_hilbert_triple_continuity
import Theorems.Thm_HunterPDE_Parabolic_integration_by_parts
import Theorems.Thm_HunterPDE_Parabolic_form_time_regularity
import Theorems.Thm_HunterPDE_Parabolic_h10_l2_dense_embeddings

/-! Reduction of `HunterPDE.Parabolic.galerkin_limit` (Hunter, Prop. 6.7) to
`galerkin_energy_estimate` (Prop. 6.6), `hilbert_triple_continuity` (Thm 6.41),
`integration_by_parts` (Thm 6.42), `h10_l2_dense_embeddings` (the Hilbert triple `H¹₀ ⊂ L² ⊂ H⁻¹`:
injective dense embeddings) and `form_time_regularity` (continuity, integrability and weak continuity
in time of the bilinear form under Assumption 6.1). Proved here: weak sequential compactness of
bounded sets in `L²(0,T;V)`, weak lower semicontinuity of the norms, passage to the limit in the
Galerkin equations (density of the Galerkin spaces), the weak time derivative of the limit, and the
initial condition `u(0) = g`. -/

set_option autoImplicit false
set_option linter.all false

section Q0ffd_I
/-! Shortcut instances for `H¹₀(Ω)` and `H⁻¹(Ω)`: each one is exactly the instance that type-class
search finds anyway (`inferInstance`), declared once with high priority so that later searches stop at
it instead of re-deriving it through the submodule / continuous-linear-map hierarchy every time.
They are `scoped` (opened in each block below, not at the final `theorem solution`), so the
statement of `solution` is elaborated with the standard instances, exactly like the target's. -/
open MeasureTheory
namespace HunterPDE.Parabolic.Q0ffdFast
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
noncomputable scoped instance (priority := high) q0ffdEMS : MeasureSpace (EuclideanSpace ℝ (Fin n)) :=
  inferInstance
noncomputable scoped instance (priority := high) q0ffdH10NACG : NormedAddCommGroup (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdH10SACG : SeminormedAddCommGroup (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdH10IPS : InnerProductSpace ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdH10NS : NormedSpace ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdH10Mod : Module ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1NACG : NormedAddCommGroup (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1SACG : SeminormedAddCommGroup (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1NS : NormedSpace ℝ (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1Mod : Module ℝ (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1CS : CompleteSpace (Hm1 n Ω) := inferInstance
end HunterPDE.Parabolic.Q0ffdFast
end Q0ffd_I

section Q0ffd_L0
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section ht
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}



/-- The embedding `L²(Ω) → H⁻¹(Ω)`, `f ↦ (v ↦ (f, v)_{L²})`. -/
noncomputable def l2Dual (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Hm1 n Ω :=
  (ContinuousLinearMap.precomp ℝ (toL2L n Ω) : _).comp (innerSL ℝ)

lemma l2Dual_apply (f : Lp ℝ 2 (volume.restrict Ω)) (v : H10 n Ω) :
    l2Dual n Ω f v = inner ℝ f (toL2L n Ω v) := rfl

lemma l2Embed_eq : l2Embed n Ω = (l2Dual n Ω).comp (toL2L n Ω) := rfl

/-- (H1) `toL2` is injective on `H¹₀`: the weak gradient of `0` is `0`. -/
lemma toL2L_injective (hΩ : IsOpen Ω) : Function.Injective (toL2L n Ω) :=
  (h10_l2_dense_embeddings hΩ).1

/-- (H3) `C_c^∞(Ω)` (hence `H¹₀`) is dense in `L²(Ω)`. -/
lemma toL2L_denseRange (hΩ : IsOpen Ω) : DenseRange (toL2L n Ω) :=
  (h10_l2_dense_embeddings hΩ).2.1

lemma l2Dual_injective (hΩ : IsOpen Ω) : Function.Injective (l2Dual n Ω) :=
  (h10_l2_dense_embeddings hΩ).2.2.1

/-- (H4) `L²(Ω)` is dense in `H⁻¹(Ω)` (via the Riesz isomorphism of `H¹₀`). -/
lemma l2Dual_denseRange (hΩ : IsOpen Ω) : DenseRange (l2Dual n Ω) :=
  (h10_l2_dense_embeddings hΩ).2.2.2

instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

lemma separable_L2 : TopologicalSpace.SeparableSpace (Lp ℝ 2 (volume.restrict Ω)) := by
  infer_instance

instance : TopologicalSpace.SeparableSpace (Jet n) := by
  haveI : ProperSpace (Jet n) := FiniteDimensional.proper ℝ _
  infer_instance

lemma separable_H10 : TopologicalSpace.SeparableSpace (H10 n Ω) := by
  have : SecondCountableTopology (JetL2 n Ω) := inferInstance
  infer_instance

/-- The Hilbert triple `H¹₀(Ω) ⊂ L²(Ω) ⊂ H⁻¹(Ω)`. -/
noncomputable def h10Triple (hΩ : IsOpen Ω) : HilbertTriple (H10 n Ω) (Lp ℝ 2 (volume.restrict Ω)) where
  toH := toL2L n Ω
  toDual := l2Dual n Ω
  injective_toH := toL2L_injective hΩ
  injective_toDual := l2Dual_injective hΩ
  denseRange_toH := toL2L_denseRange hΩ
  denseRange_toDual := l2Dual_denseRange hΩ
  separable_V := separable_H10
  separable_H := separable_L2
  pairing := fun f v => rfl

end ht

section b1
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}



/-! ## Components of `H¹₀` elements as `L²` functions -/

lemma val_ae (u : H10 n Ω) :
    (toL2L n Ω u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict Ω] val u := by
  have := (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).coeFn_compLp
    (μ := volume.restrict Ω) (p := 2) (u : JetL2 n Ω)
  filter_upwards [this] with x hx
  exact hx

/-! ## Time sections of coefficients on the cylinder -/

/-! ## The form at a good time -/

section good
variable {P : Coeffs n} {θ M t : ℝ}

end good

/-! ## Measurability of the form in time -/

end b1

section b2
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}


/-! ## `L²` inner product, coordinates and the Galerkin space -/

lemma l2inner_eq (u v : H10 n Ω) : l2inner u v = inner ℝ (toL2L n Ω u) (toL2L n Ω v) := by
  rw [l2inner, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [val_ae u, val_ae v] with x h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, Real.ringHom_apply, mul_comm]

section orth
variable {w : ℕ → H10 n Ω}

end orth


end b2

end HunterPDE.Parabolic
end Q0ffd_L0

section Q0ffd_W
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section weak
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- Sequential weak compactness of bounded sets in a separable Hilbert space. -/
theorem weak_subseq [SecondCountableTopology X] (x : ℕ → X) (R : ℝ) (hb : ∀ k, ‖x k‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : X, ∀ z : X,
      Tendsto (fun k => inner ℝ z (x (φ k))) atTop (𝓝 (inner ℝ z y)) := by
  have : TopologicalSpace.SeparableSpace X := inferInstance
  have hseq := WeakDual.isSeqCompact_closedBall ℝ X (0 : StrongDual ℝ X) R
  have hmem : ∀ k, (StrongDual.toWeakDual (innerSL ℝ (x k)) : WeakDual ℝ X) ∈
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ X) R) := by
    intro k
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
    simpa only [StrongDual.toStrongDual_toWeakDual, innerSL_apply_norm] using hb k
  have hob12 := hseq hmem
  obtain ⟨ℓ, -, φ, hφ, hlim⟩ := hob12
  refine ⟨φ, hφ, (InnerProductSpace.toDual ℝ X).symm (WeakDual.toStrongDual ℓ), fun z => ?_⟩
  have h1 := (WeakDual.eval_continuous z).tendsto ℓ |>.comp hlim
  have h2 : ∀ k, (StrongDual.toWeakDual (innerSL ℝ (x (φ k))) : WeakDual ℝ X) z
      = inner ℝ z (x (φ k)) := by
    intro k; simp only [StrongDual.toWeakDual_apply, coe_innerSL_apply, real_inner_comm]
  have h3 : ℓ z =
      inner ℝ z ((InnerProductSpace.toDual ℝ X).symm (WeakDual.toStrongDual ℓ)) := by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rfl
  rw [← h3]
  simpa only [Function.comp_def, h2] using h1

lemma norm_le_of_weak {x : ℕ → X} {y : X} {b : ℝ}
    (hw : ∀ z : X, Tendsto (fun k => inner ℝ z (x k)) atTop (𝓝 (inner ℝ z y)))
    (hb : Tendsto (fun k => ‖x k‖) atTop (𝓝 b)) : ‖y‖ ≤ b := by
  have h1 : Tendsto (fun k => inner ℝ y (x k)) atTop (𝓝 (‖y‖ ^ 2)) := by
    simpa only [inner_self_eq_norm_sq_to_K, Real.ringHom_apply] using hw y
  have h2 : Tendsto (fun k => ‖y‖ * ‖x k‖) atTop (𝓝 (‖y‖ * b)) := hb.const_mul _
  have h3 : ‖y‖ ^ 2 ≤ ‖y‖ * b :=
    le_of_tendsto_of_tendsto' h1 h2 (fun k => real_inner_le_norm _ _)
  rcases (norm_nonneg y).eq_or_lt with h | h
  · rw [← h]; exact ge_of_tendsto' hb (fun k => norm_nonneg _)
  · nlinarith

end weak

section linf
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma integrable_inner_fn {μ : Measure ℝ} {f g : ℝ → V} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun t => inner ℝ (f t) (g t)) μ := by
  have := L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  refine this.congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with t h1 h2
  rw [h1, h2]

lemma linfty_bound (J : V →L[ℝ] H) {μ : Measure ℝ} [IsFiniteMeasure μ]
    (y : ℝ → V) (hy : StronglyMeasurable y) (hy2 : MemLp y 2 μ)
    (x : ℕ → ℝ → V) (hxm : ∀ k, MemLp (x k) 2 μ)
    (hconv : ∀ Z : ℝ → V, MemLp Z 2 μ →
      Tendsto (fun k => ∫ t, inner ℝ (Z t) (x k t) ∂μ) atTop (𝓝 (∫ t, inner ℝ (Z t) (y t) ∂μ)))
    (a : ℕ → ℝ) (a0 : ℝ) (ha0 : 0 ≤ a0) (ha : Tendsto a atTop (𝓝 a0))
    (hbd : ∀ k, ∀ᵐ t ∂μ, ‖J (x k t)‖ ≤ a k) :
    ∀ᵐ t ∂μ, ‖J (y t)‖ ≤ a0 := by
  have hJy : Measurable (fun t => ‖J (y t)‖) := (J.continuous.comp_stronglyMeasurable hy).norm.measurable
  set E : Set ℝ := {t | a0 < ‖J (y t)‖} with hE
  have hEm : MeasurableSet E := measurableSet_lt measurable_const hJy
  set Z : ℝ → V := fun t => E.indicator (fun t => (ContinuousLinearMap.adjoint J) (J (y t))) t
    with hZ
  have hZm : MemLp Z 2 μ :=
    (((ContinuousLinearMap.adjoint J).comp J).comp_memLp' hy2).indicator hEm
  have hpair : ∀ (v : ℝ → V) t, inner ℝ (Z t) (v t) =
      E.indicator (fun t => inner ℝ (J (y t)) (J (v t))) t := by
    intro v t
    by_cases ht : t ∈ E
    · simp only [hZ, ht, indicator_of_mem, ContinuousLinearMap.adjoint_inner_left]
    · simp only [hZ, ht, not_false_eq_true, indicator_of_notMem, inner_zero_left]
  have hlim := hconv Z hZm
  simp_rw [hpair] at hlim
  -- right-hand side limit
  have hJyL2 : MemLp (fun t => ‖J (y t)‖) 2 μ := (J.comp_memLp' hy2).norm
  have hJyI : Integrable (fun t => ‖J (y t)‖) μ := hJyL2.integrable (by norm_num)
  have hrhs : Tendsto (fun k => ∫ t, E.indicator (fun t => ‖J (y t)‖ * a k) t ∂μ) atTop
      (𝓝 (∫ t, E.indicator (fun t => ‖J (y t)‖ * a0) t ∂μ)) := by
    have : ∀ c : ℝ, ∫ t, E.indicator (fun t => ‖J (y t)‖ * c) t ∂μ =
        c * ∫ t, E.indicator (fun t => ‖J (y t)‖) t ∂μ := by
      intro c
      rw [← integral_const_mul]
      congr 1; ext t; by_cases ht : t ∈ E <;> simp only [mul_comm, ht, indicator_of_mem, not_false_eq_true, indicator_of_notMem, mul_zero]
    simp_rw [this]
    exact ha.mul_const _
  have hle : ∀ k, ∫ t, E.indicator (fun t => inner ℝ (J (y t)) (J (x k t))) t ∂μ ≤
      ∫ t, E.indicator (fun t => ‖J (y t)‖ * a k) t ∂μ := by
    intro k
    have hI1 : Integrable (fun t => E.indicator (fun t => inner ℝ (J (y t)) (J (x k t))) t) μ := by
      have := integrable_inner_fn hZm (hxm k)
      refine this.congr (Eventually.of_forall fun t => hpair (x k) t)
    have hI2 : Integrable (fun t => E.indicator (fun t => ‖J (y t)‖ * a k) t) μ :=
      (hJyI.mul_const (a k)).indicator hEm
    refine integral_mono_ae hI1 hI2 ?_
    filter_upwards [hbd k] with t ht
    by_cases hmem : t ∈ E
    · simp only [hmem, indicator_of_mem]
      calc inner ℝ (J (y t)) (J (x k t)) ≤ ‖J (y t)‖ * ‖J (x k t)‖ := real_inner_le_norm _ _
        _ ≤ ‖J (y t)‖ * a k := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    · simp only [hmem, not_false_eq_true, indicator_of_notMem, Std.le_refl]
  have hlimle := le_of_tendsto_of_tendsto' hlim hrhs hle
  -- positivity argument
  set g : ℝ → ℝ := fun t => E.indicator (fun t => ‖J (y t)‖ * (‖J (y t)‖ - a0)) t with hg
  have hg0 : ∀ t, 0 ≤ g t := by
    intro t
    by_cases ht : t ∈ E
    · have : a0 < ‖J (y t)‖ := ht
      simp only [hg, ht, indicator_of_mem]
      exact mul_nonneg (norm_nonneg _) (by linarith)
    · simp only [hg, ht, not_false_eq_true, indicator_of_notMem, Std.le_refl]
  have hgI : Integrable g μ := by
    have h1 : Integrable (fun t => E.indicator (fun t => ‖J (y t)‖ * ‖J (y t)‖) t) μ := by
      have := (hJyL2.integrable_sq).indicator hEm
      refine this.congr (Eventually.of_forall fun t => ?_)
      by_cases ht : t ∈ E <;> simp only [sq, ht, indicator_of_mem, not_false_eq_true, indicator_of_notMem]
    have h2 : Integrable (fun t => E.indicator (fun t => ‖J (y t)‖ * a0) t) μ :=
      (hJyI.mul_const a0).indicator hEm
    refine (h1.sub h2).congr (Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ E <;> simp only [Pi.sub_apply, ht, indicator_of_mem, hg, mul_sub, not_false_eq_true, indicator_of_notMem, sub_self]
  have hgint : ∫ t, g t ∂μ ≤ 0 := by
    have h1 : Integrable (fun t => E.indicator (fun t => inner ℝ (J (y t)) (J (y t))) t) μ := by
      have := (hJyL2.integrable_sq).indicator hEm
      refine this.congr (Eventually.of_forall fun t => ?_)
      by_cases ht : t ∈ E <;> simp only [ht, indicator_of_mem, inner_self_eq_norm_sq_to_K, Real.ringHom_apply, not_false_eq_true, indicator_of_notMem]
    have h2 : Integrable (fun t => E.indicator (fun t => ‖J (y t)‖ * a0) t) μ :=
      (hJyI.mul_const a0).indicator hEm
    have : ∫ t, g t ∂μ = (∫ t, E.indicator (fun t => inner ℝ (J (y t)) (J (y t))) t ∂μ) -
        ∫ t, E.indicator (fun t => ‖J (y t)‖ * a0) t ∂μ := by
      rw [← integral_sub h1 h2]
      congr 1; ext t
      by_cases ht : t ∈ E <;> simp only [hg, mul_sub, ht, indicator_of_mem, inner_self_eq_norm_sq_to_K, Real.ringHom_apply, sq, not_false_eq_true, indicator_of_notMem, sub_self]
    rw [this]; linarith
  have hg_zero : g =ᵐ[μ] 0 := by
    have := (integral_eq_zero_iff_of_nonneg hg0 hgI).1 (le_antisymm hgint (integral_nonneg hg0))
    exact this
  filter_upwards [hg_zero] with t ht
  by_contra hcon
  rw [not_le] at hcon
  have htE : t ∈ E := hcon
  have : 0 < g t := by
    simp only [hg, htE, indicator_of_mem]
    exact mul_pos (by linarith) (by linarith)
  simp only [Pi.zero_apply] at ht
  linarith

end linf

section lpfun
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {μ : Measure ℝ}

lemma inner_toLp {f g : ℝ → V} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ t, inner ℝ (f t) (g t) ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with t h1 h2
  rw [h1, h2]

theorem weak_subseq_fun [TopologicalSpace.SeparableSpace V] [IsFiniteMeasure μ]
    (x : ℕ → ℝ → V) (hx : ∀ k, MemLp (x k) 2 μ) (R : ℝ)
    (hb : ∀ k, (eLpNorm (x k) 2 μ).toReal ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℝ → V, StronglyMeasurable y ∧ MemLp y 2 μ ∧
      ∀ Z : ℝ → V, MemLp Z 2 μ →
        Tendsto (fun k => ∫ t, inner ℝ (Z t) (x (φ k) t) ∂μ) atTop
          (𝓝 (∫ t, inner ℝ (Z t) (y t) ∂μ)) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have h2 : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨h2⟩
  have hob13 := weak_subseq (X := Lp V 2 μ) (fun k => (hx k).toLp (x k)) R
    (fun k => by rw [Lp.norm_toLp]; exact hb k)
  obtain ⟨φ, hφ, ylim, hlim⟩ := hob13
  refine ⟨φ, hφ, ⇑ylim, Lp.stronglyMeasurable ylim, Lp.memLp ylim, fun Z hZ => ?_⟩
  have := hlim (hZ.toLp Z)
  have e1 : ∀ k, inner ℝ (hZ.toLp Z) ((hx (φ k)).toLp (x (φ k))) =
      ∫ t, inner ℝ (Z t) (x (φ k) t) ∂μ := fun k => inner_toLp hZ (hx (φ k))
  have e2 : inner ℝ (hZ.toLp Z) ylim = ∫ t, inner ℝ (Z t) (ylim t) ∂μ := by
    have := inner_toLp hZ (Lp.memLp ylim)
    rwa [Lp.toLp_coeFn] at this
  simpa only [e1, e2] using this

theorem eLpNorm_le_of_weak [IsFiniteMeasure μ] {x : ℕ → ℝ → V} {y : ℝ → V}
    (hx : ∀ k, MemLp (x k) 2 μ) (hy : MemLp y 2 μ)
    (hconv : ∀ Z : ℝ → V, MemLp Z 2 μ →
      Tendsto (fun k => ∫ t, inner ℝ (Z t) (x k t) ∂μ) atTop (𝓝 (∫ t, inner ℝ (Z t) (y t) ∂μ)))
    {b : ℝ} (hb : Tendsto (fun k => (eLpNorm (x k) 2 μ).toReal) atTop (𝓝 b)) :
    (eLpNorm y 2 μ).toReal ≤ b := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have := norm_le_of_weak (X := Lp V 2 μ) (x := fun k => (hx k).toLp (x k)) (y := hy.toLp y)
    (b := b) (fun z => by
      have h := hconv ⇑z (Lp.memLp z)
      have e1 : ∀ k, inner ℝ z ((hx k).toLp (x k)) = ∫ t, inner ℝ (z t) (x k t) ∂μ := by
        intro k
        have := inner_toLp (Lp.memLp z) (hx k)
        rwa [Lp.toLp_coeFn] at this
      have e2 : inner ℝ z (hy.toLp y) = ∫ t, inner ℝ (z t) (y t) ∂μ := by
        have := inner_toLp (Lp.memLp z) hy
        rwa [Lp.toLp_coeFn] at this
      simpa only [e1, e2] using h) (by simpa only [Lp.norm_toLp] using hb)
  simpa only [ge_iff_le, Lp.norm_toLp] using this

end lpfun
end HunterPDE.Parabolic
end Q0ffd_W

section Q0ffd_R
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section riesz
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Riesz map `V → V'` as an `ℝ`-linear continuous map. -/
noncomputable def dualL : V →L[ℝ] StrongDual ℝ V :=
  LinearMap.mkContinuous
    { toFun := fun x => InnerProductSpace.toDual ℝ V x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun c x => by simp only [map_smul, Real.ringHom_apply] } 1 (fun x => by simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_map, one_mul, Std.le_refl])

/-- Inverse Riesz map `V' → V` as an `ℝ`-linear continuous map. -/
noncomputable def rzL : StrongDual ℝ V →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := fun F => (InnerProductSpace.toDual ℝ V).symm F
      map_add' := fun x y => map_add _ x y
      map_smul' := fun c x => by simp only [map_smul, Real.ringHom_apply] } 1 (fun x => by simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_map, one_mul, Std.le_refl])

variable {V}

lemma dualL_apply (x y : V) : dualL V x y = inner ℝ x y := by
  simp only [dualL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, InnerProductSpace.toDual_apply_apply]

lemma norm_dualL (x : V) : ‖dualL V x‖ = ‖x‖ := by simp only [dualL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, norm_map]

lemma inner_rzL (F : StrongDual ℝ V) (y : V) : inner ℝ (rzL V F) y = F y := by
  simp only [rzL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, InnerProductSpace.toDual_symm_apply]

lemma norm_rzL (F : StrongDual ℝ V) : ‖rzL V F‖ = ‖F‖ := by simp only [rzL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, norm_map]

end riesz

section eval
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma integral_eq_of_eval {μ : Measure ℝ} [IsFiniteMeasure μ] (S : Set (Y →L[ℝ] ℝ))
    (hsep : ∀ a b : Y, (∀ s ∈ S, s a = s b) → a = b) {g h : ℝ → Y}
    (hg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (H : ∀ s ∈ S, ∫ t, s (g t) ∂μ = ∫ t, s (h t) ∂μ) : ∫ t, g t ∂μ = ∫ t, h t ∂μ := by
  apply hsep
  intro s hs
  rw [← s.integral_comp_comm (hg.integrable (by norm_num)),
    ← s.integral_comp_comm (hh.integrable (by norm_num))]
  exact H s hs

lemma memLp_smul_bdd {μ : Measure ℝ} {a : ℝ → ℝ} {B : ℝ} (ha : AEStronglyMeasurable a μ)
    (hb : ∀ t, |a t| ≤ B) {g : ℝ → Y} (hg : MemLp g 2 μ) : MemLp (fun t => a t • g t) 2 μ := by
  refine hg.of_le_mul (c := B) (ha.smul hg.1) (Eventually.of_forall fun t => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _)

end eval

section wtd
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma hasWeakTimeDeriv_of_eval (ι : X →L[ℝ] Y) (T : ℝ) (u : ℝ → X) (w : ℝ → Y)
    (hu : MemLp u 2 (timeMeasure T)) (hw : MemLp w 2 (timeMeasure T))
    (S : Set (Y →L[ℝ] ℝ)) (hsep : ∀ a b : Y, (∀ s ∈ S, s a = s b) → a = b)
    (H : ∀ φ : ℝ → ℝ, IsTestFunctionOn T φ → ∀ s ∈ S,
      ∫ t in Set.Ioo 0 T, deriv φ t * s (ι (u t)) = -∫ t in Set.Ioo 0 T, φ t * s (w t)) :
    HasWeakTimeDeriv ι T u w := by
  have : IsFiniteMeasure (timeMeasure T) := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  intro φ hφ
  obtain ⟨hφs, hφc, hφt⟩ := hφ
  have hφ' : Continuous (deriv φ) := hφs.continuous_deriv (by simp only [WithTop.one_le_coe, le_top])
  have hφ'c : HasCompactSupport (deriv φ) := hφc.deriv
  have hob14 := hφ'.bounded_above_of_compact_support hφ'c
  obtain ⟨B1, hB1⟩ := hob14
  have hob15 := (hφs.continuous).bounded_above_of_compact_support hφc
  obtain ⟨B2, hB2⟩ := hob15
  have hg : MemLp (fun t => deriv φ t • ι (u t)) 2 (timeMeasure T) :=
    memLp_smul_bdd (B := B1) hφ'.aestronglyMeasurable (fun t => by simpa only [Real.norm_eq_abs] using hB1 t)
      (ι.comp_memLp' hu)
  have hh : MemLp (fun t => -(φ t • w t)) 2 (timeMeasure T) :=
    (memLp_smul_bdd (B := B2) hφs.continuous.aestronglyMeasurable
      (fun t => by simpa only [Real.norm_eq_abs] using hB2 t) hw).neg
  rw [← integral_neg]
  refine integral_eq_of_eval S hsep hg hh ?_
  intro s hs
  have := H φ ⟨hφs, hφc, hφt⟩ s hs
  simp only [map_smul, smul_eq_mul, map_neg, integral_neg]
  exact this

end wtd

lemma ae_zero_of_test {T : ℝ} {G : ℝ → ℝ} (hG : Integrable G (timeMeasure T))
    (h : ∀ ψ : ℝ → ℝ, IsTestFunctionOn T ψ → ∫ t in Set.Ioo 0 T, ψ t * G t = 0) :
    G =ᵐ[timeMeasure T] 0 := by
  have hloc : LocallyIntegrableOn G (Set.Ioo 0 T) volume := by
    have : IntegrableOn G (Set.Ioo 0 T) volume := hG
    exact this.locallyIntegrableOn
  have := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
    intro g hg hgc hgs
    have e : ∫ x, g x • G x = ∫ x in Set.Ioo 0 T, g x * G x := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · simp only [smul_eq_mul]
      · intro x hx
        have : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hgs h))
        simp only [this, zero_mul]
    rw [e]
    exact h g ⟨hg, hgc, hgs⟩)
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [this] with x hx hxm
  exact hx hxm

end HunterPDE.Parabolic
end Q0ffd_R

section Q0ffd_R2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section r2

lemma el_norm {E : Type*} [SeminormedAddCommGroup E] (f : ℝ → E) (p : ℝ≥0∞) (μ : Measure ℝ) :
    eLpNorm f p μ = eLpNorm (fun t => ‖f t‖) p μ :=
  eLpNorm_congr_enorm_ae (Filter.Eventually.of_forall fun x => by simp only [enorm_eq_nnnorm, nnnorm_norm])

lemma el_le {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → E} {g : ℝ → ℝ} {p : ℝ≥0∞}
    {μ : Measure ℝ} (h : ∀ᵐ t ∂μ, ‖f t‖ ≤ g t) : eLpNorm f p μ ≤ eLpNorm g p μ := by
  rw [el_norm]; exact eLpNorm_mono_ae_real (by filter_upwards [h] with t ht; simpa only [norm_norm] using ht)

lemma el_cmul_norm {E : Type*} [SeminormedAddCommGroup E] (f : ℝ → E) {a : ℝ} (ha : 0 ≤ a)
    (p : ℝ≥0∞) (μ : Measure ℝ) :
    eLpNorm (fun t => a * ‖f t‖) p μ = ENNReal.ofReal a * eLpNorm f p μ := by
  have : (fun t => a * ‖f t‖) = a • (fun t => ‖f t‖) := by funext t; simp only [Pi.smul_apply, smul_eq_mul]
  rw [this, eLpNorm_const_smul, ← el_norm, Real.enorm_eq_ofReal ha]

lemma comp_memLp_semi {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : ℝ → E} {p : ℝ≥0∞}
    {μ : Measure ℝ} (hf : MemLp f p μ) : MemLp (fun t => L (f t)) p μ := by
  refine ⟨L.continuous.comp_aestronglyMeasurable hf.1, ?_⟩
  refine (el_le (g := fun t => ‖L‖ * ‖f t‖)
    (Filter.Eventually.of_forall fun t => L.le_opNorm _)).trans_lt ?_
  rw [el_cmul_norm f (norm_nonneg L)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2

lemma scalar_of_hasWeakTimeDeriv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (T : ℝ) (x y : ℝ → X) (hx : MemLp x 2 (timeMeasure T))
    (hy : MemLp y 2 (timeMeasure T))
    (h : HasWeakTimeDeriv (ContinuousLinearMap.id ℝ X) T x y) (s : X →L[ℝ] ℝ) (φ : ℝ → ℝ)
    (hφ : IsTestFunctionOn T φ) :
    ∫ t in Set.Ioo 0 T, deriv φ t * s (x t) = -∫ t in Set.Ioo 0 T, φ t * s (y t) := by
  have : IsFiniteMeasure (timeMeasure T) := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  obtain ⟨hφs, hφc, hφt⟩ := hφ
  have hφ' : Continuous (deriv φ) := hφs.continuous_deriv (by simp only [WithTop.one_le_coe, le_top])
  have hφ'c : HasCompactSupport (deriv φ) := hφc.deriv
  have hob16 := hφ'.bounded_above_of_compact_support hφ'c
  obtain ⟨B1, hB1⟩ := hob16
  have hob17 := (hφs.continuous).bounded_above_of_compact_support hφc
  obtain ⟨B2, hB2⟩ := hob17
  have hg : MemLp (fun t => deriv φ t • x t) 2 (timeMeasure T) :=
    memLp_smul_bdd (B := B1) hφ'.aestronglyMeasurable (fun t => by simpa only [Real.norm_eq_abs] using hB1 t) hx
  have hh : MemLp (fun t => φ t • y t) 2 (timeMeasure T) :=
    memLp_smul_bdd (B := B2) hφs.continuous.aestronglyMeasurable
      (fun t => by simpa only [Real.norm_eq_abs] using hB2 t) hy
  have h1 := h φ ⟨hφs, hφc, hφt⟩
  simp only [ContinuousLinearMap.id_apply] at h1
  have h2 := congrArg s h1
  rw [map_neg, ← s.integral_comp_comm (hg.integrable (by norm_num)),
    ← s.integral_comp_comm (hh.integrable (by norm_num))] at h2
  simpa only [map_smul, smul_eq_mul] using h2

lemma l2Embed_apply {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (a b : H10 n Ω) :
    l2Embed n Ω a b = inner ℝ (toL2L n Ω a) (toL2L n Ω b) := by
  rw [l2Embed_eq]; simp only [ContinuousLinearMap.comp_apply, l2Dual_apply]

lemma l2Embed_symm {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (a b : H10 n Ω) :
    l2Embed n Ω a b = l2Embed n Ω b a := by
  rw [l2Embed_apply, l2Embed_apply, real_inner_comm]

lemma l2Embed_eq_l2inner {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (a b : H10 n Ω) :
    l2Embed n Ω a b = l2inner a b := by
  rw [l2Embed_apply, l2inner_eq]

/-- evaluation functionals separate points of `Hm1`. -/
lemma hm1_sep {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} :
    ∀ a b : Hm1 n Ω, (∀ s ∈ {s : Hm1 n Ω →L[ℝ] ℝ | ∃ v : H10 n Ω,
      s = ContinuousLinearMap.apply ℝ ℝ v}, s a = s b) → a = b := by
  intro a b hab
  ext v
  exact hab _ ⟨v, rfl⟩

/-- `hasWeakTimeDeriv_of_eval` for `H¹₀ → H⁻¹`, tested against the evaluations `s = (· v)`. -/
lemma hwtd_hm1 {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (ι : H10 n Ω →L[ℝ] Hm1 n Ω) (T : ℝ)
    (u : ℝ → H10 n Ω) (w : ℝ → Hm1 n Ω)
    (hu : MemLp u 2 (timeMeasure T)) (hw : MemLp w 2 (timeMeasure T))
    (H : ∀ φ : ℝ → ℝ, IsTestFunctionOn T φ → ∀ v : H10 n Ω,
      ∫ t in Set.Ioo 0 T, deriv φ t * ι (u t) v = -∫ t in Set.Ioo 0 T, φ t * w t v) :
    HasWeakTimeDeriv ι T u w := by
  have H' : ∀ φ : ℝ → ℝ, IsTestFunctionOn T φ →
      ∀ s ∈ {s : Hm1 n Ω →L[ℝ] ℝ | ∃ v : H10 n Ω, s = ContinuousLinearMap.apply ℝ ℝ v},
      ∫ t in Set.Ioo 0 T, deriv φ t * s (ι (u t)) = -∫ t in Set.Ioo 0 T, φ t * s (w t) := by
    rintro φ hφ _ ⟨v, rfl⟩
    exact H φ hφ v
  have key := hasWeakTimeDeriv_of_eval (X := H10 n Ω) (Y := Hm1 n Ω) ι T u w hu hw _ hm1_sep H'
  exact key

set_option maxHeartbeats 1600000 in
lemma galerkin_hwd_l2Embed {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (T : ℝ)
    (x y : ℝ → H10 n Ω) (hx : MemLp x 2 (timeMeasure T)) (hy : MemLp y 2 (timeMeasure T))
    (h : HasWeakTimeDeriv (ContinuousLinearMap.id ℝ (H10 n Ω)) T x y) :
    HasWeakTimeDeriv (l2Embed n Ω) T x (fun t => l2Embed n Ω (y t)) := by
  have hw : MemLp (fun t => l2Embed n Ω (y t)) 2 (timeMeasure T) :=
    by convert comp_memLp_semi (E := H10 n Ω) (F := Hm1 n Ω) (l2Embed n Ω) hy
  refine hwtd_hm1 (l2Embed n Ω) T x (fun t => l2Embed n Ω (y t)) hx hw ?_
  intro φ hφ v
  exact scalar_of_hasWeakTimeDeriv T x y hx hy h
    ((ContinuousLinearMap.apply ℝ ℝ v).comp (l2Embed n Ω)) φ hφ

end r2
end HunterPDE.Parabolic
end Q0ffd_R2

section Q0ffd_F
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section F
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

section lam
variable {T : ℝ} {P : Coeffs n} {θ M : ℝ}

end lam

end F
end HunterPDE.Parabolic
end Q0ffd_F

section Q0ffd_D
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section D
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma inner_H10 (u v : H10 n Ω) :
    inner ℝ u v = l2inner u v + ∫ x in Ω, inner ℝ (grad u x) (grad v x) := by
  have hpt : ∀ x, inner ℝ ((u : JetL2 n Ω) x) ((v : JetL2 n Ω) x) =
      val u x * val v x + inner ℝ (grad u x) (grad v x) := fun x => by
    rw [WithLp.prod_inner_apply]
    simp only [WithLp.ofLp_fst, RCLike.inner_apply, Real.ringHom_apply, mul_comm, WithLp.ofLp_snd, val, grad]
  have htot := L2.integrable_inner (𝕜 := ℝ) (u : JetL2 n Ω) (v : JetL2 n Ω)
  have hv : Integrable (fun x => val u x * val v x) (volume.restrict Ω) := by
    have h := L2.integrable_inner (𝕜 := ℝ) (toL2L n Ω u) (toL2L n Ω v)
    refine h.congr ?_
    filter_upwards [val_ae u, val_ae v] with x h1 h2
    rw [h1, h2]
    simp only [RCLike.inner_apply, Real.ringHom_apply, mul_comm]
  have hg : Integrable (fun x => inner ℝ (grad u x) (grad v x)) (volume.restrict Ω) := by
    refine (htot.sub hv).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [hpt x]
    ring
  rw [Submodule.coe_inner, L2.inner_def, l2inner, ← integral_add hv hg]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

lemma eig_nonneg {w : ℕ → H10 n Ω} {eig : ℕ → ℝ} (h : IsDirichletEigenbasis Ω w eig) (k : ℕ) :
    0 ≤ eig k := by
  have h1 := h.1 k (w k)
  have h2 := h.2.1 k k
  rw [if_pos rfl] at h2
  rw [h2, mul_one] at h1
  rw [← h1]
  exact integral_nonneg (fun x => real_inner_self_nonneg)

lemma galerkinSpace_mono (w : ℕ → H10 n Ω) : Monotone (galerkinSpace w) := by
  intro N M hNM
  exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hNM))

lemma dense_galerkin (hinj : Function.Injective (toL2L n Ω)) {w : ℕ → H10 n Ω} {eig : ℕ → ℝ}
    (h : IsDirichletEigenbasis Ω w eig) :
    Dense (⋃ N, (galerkinSpace w N : Set (H10 n Ω))) := by
  set S : Submodule ℝ (H10 n Ω) := ⨆ N, galerkinSpace w N with hS
  have hcoe : (S : Set (H10 n Ω)) = ⋃ N, (galerkinSpace w N : Set (H10 n Ω)) :=
    Submodule.coe_iSup_of_directed _ (galerkinSpace_mono w).directed_le
  rw [← hcoe]
  refine Submodule.dense_iff_topologicalClosure_eq_top.2 ?_
  refine (Submodule.topologicalClosure_eq_top_iff).2 ?_
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hwS : ∀ k, w k ∈ S := fun k =>
    (le_iSup (galerkinSpace w) (k + 1)) (Submodule.subset_span ⟨k, by simp only [mem_Iio, lt_add_iff_pos_right, Order.lt_one_iff], rfl⟩)
  have hl2 : ∀ k, l2inner (w k) v = 0 := by
    intro k
    have h0 : inner ℝ (w k) v = 0 := by
      rw [real_inner_comm]; exact (Submodule.mem_orthogonal' _ _).1 hv (w k) (hwS k)
    rw [inner_H10, h.1 k v] at h0
    have h1 : (1 + eig k) * l2inner (w k) v = 0 := by linarith
    have h2 : (1 + eig k) ≠ 0 := by have := eig_nonneg h k; linarith
    exact (mul_eq_zero.1 h1).resolve_left h2
  have hperp : (Submodule.span ℝ (Set.range fun k => toL2 (w k))) ≤
      (Submodule.span ℝ {toL2L n Ω v})ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    have := hl2 k
    rw [l2inner_eq] at this
    rw [real_inner_comm]
    exact this
  have hle := Submodule.topologicalClosure_minimal _ hperp (Submodule.isClosed_orthogonal _)
  rw [h.2.2] at hle
  have hmem : toL2L n Ω v ∈ (Submodule.span ℝ {toL2L n Ω v})ᗮ := hle trivial
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hmem
  have : toL2L n Ω v = 0 := inner_self_eq_zero.1 hmem
  exact hinj (by simpa only [map_zero] using this)

lemma exists_countable_dense_sub {X : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X]
    (A : Set X) (hA : Dense A) : ∃ D : Set X, D.Countable ∧ D ⊆ A ∧ Dense D := by
  have hob20 := (TopologicalSpace.IsSeparable.of_separableSpace A).exists_countable_dense_subset
  obtain ⟨D, hDA, hDc, hAD⟩ := hob20
  refine ⟨D, hDc, hDA, ?_⟩
  rw [dense_iff_closure_eq]
  refine eq_univ_of_univ_subset ?_
  calc (univ : Set X) = closure A := hA.closure_eq.symm
    _ ⊆ closure (closure D) := closure_mono hAD
    _ = closure D := closure_closure

end D
end HunterPDE.Parabolic
end Q0ffd_D

section Q0ffd_D2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section D2
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma toL2_eq (u : H10 n Ω) : toL2 u = toL2L n Ω u := rfl

lemma toL2L_galerkinProj (w : ℕ → H10 n Ω) (N : ℕ) (g : Lp ℝ 2 (volume.restrict Ω)) :
    toL2L n Ω (galerkinProj w N g) =
      ∑ k ∈ Finset.range N, inner ℝ (toL2 (w k)) g • toL2L n Ω (w k) := by
  unfold galerkinProj
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.map_smul]

lemma galerkinProj_tendsto {w : ℕ → H10 n Ω} {eig : ℕ → ℝ} (h : IsDirichletEigenbasis Ω w eig)
    (g : Lp ℝ 2 (volume.restrict Ω)) :
    Tendsto (fun N => toL2L n Ω (galerkinProj w N g)) atTop (𝓝 g) := by
  have ho : Orthonormal ℝ (fun k => toL2 (w k)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have := h.2.1 i j
    rw [l2inner_eq] at this
    exact this
  have hsp : (Submodule.span ℝ (Set.range fun k => toL2 (w k)))ᗮ = ⊥ :=
    Submodule.topologicalClosure_eq_top_iff.1 h.2.2
  let b := HilbertBasis.mkOfOrthogonalEqBot ho hsp
  have hb : ∀ k, b k = toL2 (w k) := fun k => by simp only [HilbertBasis.coe_mkOfOrthogonalEqBot, b]
  have hs := b.hasSum_repr g
  have := hs.tendsto_sum_nat
  convert this using 2 with N
  rw [toL2L_galerkinProj]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [HilbertBasis.repr_apply_apply, hb]
  rfl

end D2
end HunterPDE.Parabolic
end Q0ffd_D2

section Q0ffd_P1
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section limit
lemma h10_inner_smul_left {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (c : ℝ) (a b : H10 n Ω) :
    inner ℝ (c • a) b = c * inner ℝ a b := by
  rw [Submodule.coe_inner, Submodule.coe_smul, real_inner_smul_left, ← Submodule.coe_inner]

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}

set_option maxHeartbeats 1600000 in
theorem limit_hasWeakTimeDeriv [IsFiniteMeasure (timeMeasure T)]
    {u zl : ℝ → H10 n Ω} (hu : MemLp u 2 (timeMeasure T)) (hzl : MemLp zl 2 (timeMeasure T))
    {x y : ℕ → ℝ → H10 n Ω}
    (hx : ∀ k, MemLp (x k) 2 (timeMeasure T)) (hy : ∀ k, MemLp (y k) 2 (timeMeasure T))
    (hxy : ∀ k, HasWeakTimeDeriv (ContinuousLinearMap.id ℝ (H10 n Ω)) T (x k) (y k))
    (hxc : ∀ Z : ℝ → H10 n Ω, MemLp Z 2 (timeMeasure T) →
      Tendsto (fun k => ∫ t, inner ℝ (Z t) (x k t) ∂(timeMeasure T)) atTop
        (𝓝 (∫ t, inner ℝ (Z t) (u t) ∂(timeMeasure T))))
    (hzc : ∀ Z : ℝ → H10 n Ω, MemLp Z 2 (timeMeasure T) →
      Tendsto (fun k => ∫ t, inner ℝ (Z t) (rzL (H10 n Ω) (l2Embed n Ω (y k t)))
        ∂(timeMeasure T)) atTop
        (𝓝 (∫ t, inner ℝ (Z t) (zl t) ∂(timeMeasure T)))) :
    HasWeakTimeDeriv (l2Embed n Ω) T u (fun t => dualL (H10 n Ω) (zl t)) := by
  have hw : MemLp (fun t => dualL (H10 n Ω) (zl t)) 2 (timeMeasure T) :=
    by convert comp_memLp_semi (E := H10 n Ω) (F := Hm1 n Ω) (dualL (H10 n Ω)) hzl
  refine hwtd_hm1 (l2Embed n Ω) T u (fun t => dualL (H10 n Ω) (zl t)) hu hw ?_
  intro φ hφ v
  obtain ⟨hφs, hφc, hφt⟩ := hφ
  have hφ' : Continuous (deriv φ) := hφs.continuous_deriv (by simp only [WithTop.one_le_coe, le_top])
  have hφ'c : HasCompactSupport (deriv φ) := hφc.deriv
  have hob21 := hφ'.bounded_above_of_compact_support hφ'c
  obtain ⟨B1, hB1⟩ := hob21
  have hob22 := (hφs.continuous).bounded_above_of_compact_support hφc
  obtain ⟨B2, hB2⟩ := hob22
  have hk : ∀ k, ∫ t in Set.Ioo 0 T, deriv φ t * l2Embed n Ω (x k t) v =
      -∫ t in Set.Ioo 0 T, φ t * l2Embed n Ω (y k t) v := fun k =>
    scalar_of_hasWeakTimeDeriv T (x k) (y k) (hx k) (hy k) (hxy k)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (l2Embed n Ω)) φ ⟨hφs, hφc, hφt⟩
  have hob23 : ∃ r : H10 n Ω, r = rzL (H10 n Ω) (l2Embed n Ω v) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ := hob23
  have hL : Tendsto (fun k => ∫ t in Set.Ioo 0 T, deriv φ t * l2Embed n Ω (x k t) v) atTop
      (𝓝 (∫ t in Set.Ioo 0 T, deriv φ t * l2Embed n Ω (u t) v)) := by
    have := hxc (fun t => deriv φ t • r)
      (memLp_smul_bdd (B := B1) hφ'.aestronglyMeasurable (fun t => by simpa only [Real.norm_eq_abs] using hB1 t)
        (memLp_const r))
    have e : ∀ (a : H10 n Ω) (t : ℝ), inner ℝ (deriv φ t • r) a =
        deriv φ t * l2Embed n Ω a v := by
      intro a t; rw [h10_inner_smul_left, hr, inner_rzL, l2Embed_symm]
    simp only [e] at this
    exact this
  have hR : Tendsto (fun k => ∫ t in Set.Ioo 0 T, φ t * l2Embed n Ω (y k t) v) atTop
      (𝓝 (∫ t in Set.Ioo 0 T, φ t * dualL (H10 n Ω) (zl t) v)) := by
    have := hzc (fun t => φ t • v)
      (memLp_smul_bdd (B := B2) hφs.continuous.aestronglyMeasurable
        (fun t => by simpa only [Real.norm_eq_abs] using hB2 t) (memLp_const v))
    have e : ∀ (a : H10 n Ω) (t : ℝ), inner ℝ (φ t • v) (rzL (H10 n Ω) (l2Embed n Ω a)) =
        φ t * l2Embed n Ω a v := by
      intro a t; rw [h10_inner_smul_left, real_inner_comm, inner_rzL]
    have e2 : ∀ t : ℝ, inner ℝ (φ t • v) (zl t) = φ t * dualL (H10 n Ω) (zl t) v := by
      intro t; rw [h10_inner_smul_left, real_inner_comm, dualL_apply]
    simp only [e, e2] at this
    exact this
  have hfun : (fun k => ∫ t in Set.Ioo 0 T, deriv φ t * l2Embed n Ω (x k t) v) =
      fun k => -∫ t in Set.Ioo 0 T, φ t * l2Embed n Ω (y k t) v := funext hk
  rw [hfun] at hL
  exact tendsto_nhds_unique hL hR.neg

end limit
end HunterPDE.Parabolic
end Q0ffd_P1

section Q0ffd_P2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section eqn
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}

lemma memLp_f_apply (f : ℝ → Hm1 n Ω) (hf : MemLp f 2 (timeMeasure T)) (v : H10 n Ω) :
    MemLp (fun t => f t v) 2 (timeMeasure T) := by
  convert comp_memLp_semi (E := Hm1 n Ω) (F := ℝ) (ContinuousLinearMap.apply ℝ ℝ v) hf <;> rfl

lemma memLp_l2inner (v : H10 n Ω) {y : ℝ → H10 n Ω} (hy : MemLp y 2 (timeMeasure T)) :
    MemLp (fun t => l2inner (y t) v) 2 (timeMeasure T) := by
  have := ((toL2L n Ω).comp_memLp' hy).inner_const (𝕜 := ℝ) (toL2L n Ω v)
  convert this using 2 with t
  rw [l2inner_eq]; rfl

set_option maxHeartbeats 1600000 in
theorem limit_equation [IsFiniteMeasure (timeMeasure T)]
    [TopologicalSpace.SeparableSpace (H10 n Ω)]
    {P : Coeffs n} (hP : P.Assumption61 Ω T)
    {f : ℝ → Hm1 n Ω} (hf : MemLp f 2 (timeMeasure T))
    (hinj : Function.Injective (toL2L n Ω))
    {w : ℕ → H10 n Ω} {eig : ℕ → ℝ} (heig : IsDirichletEigenbasis Ω w eig)
    {u zl : ℝ → H10 n Ω} (hu : MemLp u 2 (timeMeasure T)) (hzl : MemLp zl 2 (timeMeasure T))
    {x y : ℕ → ℝ → H10 n Ω} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hx : ∀ k, MemLp (x k) 2 (timeMeasure T)) (hy : ∀ k, MemLp (y k) 2 (timeMeasure T))
    (hGal : ∀ k, ∀ v ∈ galerkinSpace w (N k), ∀ᵐ t ∂(timeMeasure T),
      l2inner (y k t) v + form P t (x k t) v = f t v)
    (hxc : ∀ Z : ℝ → H10 n Ω, MemLp Z 2 (timeMeasure T) →
      Tendsto (fun k => ∫ t, inner ℝ (Z t) (x k t) ∂(timeMeasure T)) atTop
        (𝓝 (∫ t, inner ℝ (Z t) (u t) ∂(timeMeasure T))))
    (hzc : ∀ Z : ℝ → H10 n Ω, MemLp Z 2 (timeMeasure T) →
      Tendsto (fun k => ∫ t, inner ℝ (Z t) (rzL (H10 n Ω) (l2Embed n Ω (y k t)))
        ∂(timeMeasure T)) atTop
        (𝓝 (∫ t, inner ℝ (Z t) (zl t) ∂(timeMeasure T)))) :
    ∀ v : H10 n Ω, ∀ᵐ t ∂(timeMeasure T), dualL (H10 n Ω) (zl t) v + form P t (u t) v = f t v := by
  have hob24 := form_time_regularity hP
  obtain ⟨hFcont, hFint, hFconv⟩ := hob24
  have hzv : ∀ v : H10 n Ω, MemLp (fun t => dualL (H10 n Ω) (zl t) v) 2 (timeMeasure T) := by
    intro v
    have := hzl.inner_const (𝕜 := ℝ) v
    convert this using 2 with t
    rw [dualL_apply]
  -- Step 1
  have step1 : ∀ N0 : ℕ, ∀ v ∈ galerkinSpace w N0, ∀ ψ : ℝ → ℝ, IsTestFunctionOn T ψ →
      ∫ t in Set.Ioo 0 T, ψ t * (dualL (H10 n Ω) (zl t) v + form P t (u t) v - f t v) = 0 := by
    intro N0 v hv ψ hψ
    obtain ⟨hψs, hψc, hψt⟩ := hψ
    have hob25 := hψs.continuous.bounded_above_of_compact_support hψc
    obtain ⟨B, hB⟩ := hob25
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    have hψb : ∀ t ∈ Set.Ioo 0 T, |ψ t| ≤ B := fun t _ => by simpa only [Real.norm_eq_abs] using hB t
    have hψm : Measurable ψ := hψs.continuous.measurable
    have hψbd : ∀ t, |ψ t| ≤ B := fun t => by simpa only [Real.norm_eq_abs] using hB t
    have hA : Tendsto (fun k => ∫ t in Set.Ioo 0 T, ψ t * l2inner (y k t) v) atTop
        (𝓝 (∫ t in Set.Ioo 0 T, ψ t * dualL (H10 n Ω) (zl t) v)) := by
      have := hzc (fun t => ψ t • v)
        (memLp_smul_bdd (B := B) hψs.continuous.aestronglyMeasurable hψbd (memLp_const v))
      have e : ∀ (a : H10 n Ω) (t : ℝ), inner ℝ (ψ t • v) (rzL (H10 n Ω) (l2Embed n Ω a)) =
          ψ t * l2inner a v := by
        intro a t; rw [h10_inner_smul_left, real_inner_comm, inner_rzL, l2Embed_eq_l2inner]
      have e2 : ∀ t : ℝ, inner ℝ (ψ t • v) (zl t) = ψ t * dualL (H10 n Ω) (zl t) v := by
        intro t; rw [h10_inner_smul_left, real_inner_comm, dualL_apply]
      simp only [e, e2] at this
      exact this
    have hF := hFconv hψm hB0 hψb v hx hu hxc
    have hint : ∀ {g : ℝ → ℝ}, MemLp g 2 (timeMeasure T) →
        Integrable (fun t => ψ t * g t) (timeMeasure T) := by
      intro g hg
      have := memLp_smul_bdd (B := B) hψs.continuous.aestronglyMeasurable hψbd hg
      exact (this.integrable (by norm_num)).congr (Eventually.of_forall fun t => by simp only [smul_eq_mul])
    have hev : ∀ᶠ k in atTop,
        (∫ t in Set.Ioo 0 T, ψ t * l2inner (y k t) v) +
          ∫ t in Set.Ioo 0 T, ψ t * form P t (x k t) v =
        ∫ t in Set.Ioo 0 T, ψ t * f t v := by
      filter_upwards [hN.eventually_ge_atTop N0] with k hk
      have hvk : v ∈ galerkinSpace w (N k) := galerkinSpace_mono w hk hv
      have h1 := hint (memLp_l2inner v (hy k))
      have h2 := hFint hψm hB0 hψb v (hx k)
      rw [← integral_add h1 h2]
      refine integral_congr_ae ?_
      filter_upwards [hGal k v hvk] with t ht
      rw [← mul_add, ht]
    have hlim := hA.add hF
    have hconst : Tendsto (fun _ : ℕ => ∫ t in Set.Ioo 0 T, ψ t * f t v) atTop
        (𝓝 (∫ t in Set.Ioo 0 T, ψ t * f t v)) := tendsto_const_nhds
    have key := tendsto_nhds_unique_of_eventuallyEq hlim hconst hev
    have i1 := hint (hzv v)
    have i2 := hFint hψm hB0 hψb v hu
    have i3 := hint (memLp_f_apply f hf v)
    have e3 : ∫ t in Set.Ioo 0 T, ψ t * (dualL (H10 n Ω) (zl t) v + form P t (u t) v - f t v) =
        (∫ t in Set.Ioo 0 T, ψ t * dualL (H10 n Ω) (zl t) v) +
          (∫ t in Set.Ioo 0 T, ψ t * form P t (u t) v) - ∫ t in Set.Ioo 0 T, ψ t * f t v := by
      have hsub : Integrable (fun t => ψ t * dualL (H10 n Ω) (zl t) v + ψ t * form P t (u t) v)
          (timeMeasure T) := i1.add i2
      have hpt : ∀ t, ψ t * (dualL (H10 n Ω) (zl t) v + form P t (u t) v - f t v) =
          (ψ t * dualL (H10 n Ω) (zl t) v + ψ t * form P t (u t) v) - ψ t * f t v := by
        intro t; ring
      simp_rw [hpt]
      rw [integral_sub hsub i3, integral_add i1 i2]
    rw [e3]
    linarith only [key]
  -- Step 2
  have step2 : ∀ N0 : ℕ, ∀ v ∈ galerkinSpace w N0, ∀ᵐ t ∂(timeMeasure T),
      dualL (H10 n Ω) (zl t) v + form P t (u t) v - f t v = 0 := by
    intro N0 v hv
    have hG : Integrable (fun t => dualL (H10 n Ω) (zl t) v + form P t (u t) v - f t v)
        (timeMeasure T) := by
      have i1 := (hzv v).integrable (by norm_num)
      have i2 := hFint (ψ := fun _ => (1:ℝ)) measurable_const
        (B := 1) zero_le_one (fun t _ => by simp only [abs_one, Std.le_refl]) v hu
      have i3 := (memLp_f_apply f hf v).integrable (by norm_num)
      refine ((i1.add (i2.congr (Eventually.of_forall fun t => by simp only [one_mul]))).sub i3)
    exact ae_zero_of_test hG (step1 N0 v hv)
  -- Step 3
  have hob26 := exists_countable_dense_sub _ (dense_galerkin hinj heig)
  obtain ⟨D, hDc, hDA, hDd⟩ := hob26
  have hae : ∀ᵐ t ∂(timeMeasure T), ∀ v ∈ D,
      dualL (H10 n Ω) (zl t) v + form P t (u t) v - f t v = 0 := by
    rw [ae_ball_iff hDc]
    intro v hv
    have hob27 := Set.mem_iUnion.1 (hDA hv)
    obtain ⟨N0, hN0⟩ := hob27
    exact step2 N0 v hN0
  intro v
  filter_upwards [hae, hFcont] with t ht hg
  have hcont : Continuous (fun v : H10 n Ω =>
      dualL (H10 n Ω) (zl t) v + form P t (u t) v - f t v) :=
    ((dualL (H10 n Ω) (zl t)).continuous.add (hg (u t))).sub (f t).continuous
  have h0 := Continuous.ext_on hDd hcont continuous_const (fun v hv => by simpa only [] using ht v hv) 
  have h1 : dualL (H10 n Ω) (zl t) v + form P t (u t) v - f t v = 0 := congrFun h0 v
  linarith only [h1]

end eqn
end HunterPDE.Parabolic
end Q0ffd_P2

section Q0ffd_P3
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section ibp
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}

/-- scalar integration by parts against the linear weight `1 - t/T`. -/
lemma scalar_ibp_lambda (hT : 0 < T) {φ : ℝ → ℝ} (hφ : IsTestFunctionOn T φ) :
    ∫ t in Set.Ioo 0 T, deriv φ t * (1 - t / T) = (1 / T) * ∫ t in Set.Ioo 0 T, φ t := by
  obtain ⟨hφs, hφc, hφt⟩ := hφ
  have hd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x =>
    ((hφs.differentiable (by simp only [ne_eq, WithTop.coe_eq_zero, ENat.top_ne_zero, not_false_eq_true])) x).hasDerivAt
  have hφ' : Continuous (deriv φ) := hφs.continuous_deriv (by simp only [WithTop.one_le_coe, le_top])
  have h0 : φ 0 = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
    have := hφt h; simp only [mem_Ioo, lt_self_iff_false, false_and] at this)
  have hT0 : φ T = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
    have := hφt h; simp only [mem_Ioo, lt_self_iff_false, and_false] at this)
  have hw : ∀ x, HasDerivAt (fun t : ℝ => 1 - t / T) (-(1 / T)) x := fun x => by
    have := ((hasDerivAt_id x).div_const T).const_sub 1
    simpa only [one_div, id_eq] using this
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := T)
    (u := fun t => 1 - t / T) (v := φ) (u' := fun _ => -(1 / T)) (v' := deriv φ)
    (fun x _ => hw x) (fun x _ => hd x)
    (by exact continuous_const.intervalIntegrable _ _)
    (hφ'.intervalIntegrable _ _)
  have e1 : ∫ t in Set.Ioo 0 T, deriv φ t * (1 - t / T) =
      ∫ t in (0:ℝ)..T, (1 - t / T) * deriv φ t := by
    rw [intervalIntegral.integral_of_le hT.le, ← integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => by ring)
  have e2 : ∫ t in Set.Ioo 0 T, φ t = ∫ t in (0:ℝ)..T, φ t := by
    rw [intervalIntegral.integral_of_le hT.le, ← integral_Ioc_eq_integral_Ioo]
  have key' : ∫ x in (0:ℝ)..T, (1 - x / T) * deriv φ x = -∫ x in (0:ℝ)..T, (-(1 / T)) * φ x := by
    have := key
    simp only [h0, hT0, mul_zero, sub_zero, zero_sub, sub_self] at this
    exact this
  have e3 : ∫ x in (0:ℝ)..T, (-(1 / T)) * φ x = -((1 / T) * ∫ x in (0:ℝ)..T, φ x) := by
    rw [intervalIntegral.integral_const_mul]; ring
  rw [e1, e2, key', e3]; ring

/-- The integration-by-parts child specialised to the triple `H¹₀ ⊂ L² ⊂ H⁻¹`. -/
def IBPHyp (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ) : Prop :=
  ∀ (u v : ℝ → H10 n Ω) (ut vt : ℝ → Hm1 n Ω), MemLp u 2 (timeMeasure T) →
    MemLp v 2 (timeMeasure T) → MemLp ut 2 (timeMeasure T) → MemLp vt 2 (timeMeasure T) →
    HasWeakTimeDeriv (l2Embed n Ω) T u ut → HasWeakTimeDeriv (l2Embed n Ω) T v vt →
    ∀ (uc vc : ℝ → Lp ℝ 2 (volume.restrict Ω)), ContinuousOn uc (Set.Icc 0 T) →
      ContinuousOn vc (Set.Icc 0 T) →
      (∀ᵐ t ∂(timeMeasure T), uc t = toL2L n Ω (u t)) →
      (∀ᵐ t ∂(timeMeasure T), vc t = toL2L n Ω (v t)) →
      ∫ t in Set.Ioo 0 T, ut t (v t) =
        inner ℝ (uc T) (vc T) - inner ℝ (uc 0) (vc 0) - ∫ t in Set.Ioo 0 T, vt t (u t)

set_option maxHeartbeats 1600000 in
theorem ibp_lambda (hT : 0 < T) (hibp : IBPHyp n Ω T) {y : ℝ → H10 n Ω} {yt : ℝ → Hm1 n Ω}
    (hy : MemLp y 2 (timeMeasure T)) (hyt : MemLp yt 2 (timeMeasure T))
    (hd : HasWeakTimeDeriv (l2Embed n Ω) T y yt)
    {yc : ℝ → Lp ℝ 2 (volume.restrict Ω)} (hyc : ContinuousOn yc (Set.Icc 0 T))
    (hyce : ∀ᵐ t ∂(timeMeasure T), yc t = toL2L n Ω (y t)) (v₀ : H10 n Ω) :
    ∫ t in Set.Ioo 0 T, yt t ((1 - t / T) • v₀) =
      - inner ℝ (yc 0) (toL2L n Ω v₀) + (1 / T) * ∫ t in Set.Ioo 0 T, l2Embed n Ω v₀ (y t) := by
  have hfin : IsFiniteMeasure (timeMeasure T) := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hcont : Continuous (fun t : ℝ => 1 - t / T) := continuous_const.sub (continuous_id.div_const T)
  have hlam : ∀ t ∈ Set.Ioo 0 T, |1 - t / T| ≤ 1 := by
    intro t ht
    have h1 : 0 < t / T := div_pos ht.1 hT
    have h2 : t / T < 1 := (div_lt_one hT).2 ht.2
    rw [abs_of_pos (by linarith)]; linarith
  have hv : MemLp (fun t : ℝ => (1 - t / T) • v₀) 2 (timeMeasure T) := by
    refine MemLp.of_bound (hcont.smul continuous_const).aestronglyMeasurable ‖v₀‖ ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hlam t ht)
  have hvt : MemLp (fun _ : ℝ => (-(1 / T)) • l2Embed n Ω v₀) 2 (timeMeasure T) := by
    convert memLp_const ((-(1 / T)) • l2Embed n Ω v₀) (μ := timeMeasure T) (p := 2)
  have hdv : HasWeakTimeDeriv (l2Embed n Ω) T (fun t : ℝ => (1 - t / T) • v₀)
      (fun _ : ℝ => (-(1 / T)) • l2Embed n Ω v₀) := by
    refine hwtd_hm1 (l2Embed n Ω) T _ _ hv hvt ?_
    intro φ hφ a
    have h1 := scalar_ibp_lambda hT hφ
    have e1 : ∀ t : ℝ, deriv φ t * l2Embed n Ω ((1 - t / T) • v₀) a =
        l2Embed n Ω v₀ a * (deriv φ t * (1 - t / T)) := by
      intro t; simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
    have e2 : ∀ t : ℝ, φ t * ((-(1 / T)) • l2Embed n Ω v₀) a =
        -(1 / T) * l2Embed n Ω v₀ a * φ t := by
      intro t; simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
    simp_rw [e1, e2]
    rw [integral_const_mul, h1, integral_const_mul]
    ring
  have hvc : ContinuousOn (fun t : ℝ => (1 - t / T) • toL2L n Ω v₀) (Set.Icc 0 T) :=
    (hcont.smul continuous_const).continuousOn
  have key := hibp y (fun t : ℝ => (1 - t / T) • v₀) yt (fun _ : ℝ => (-(1 / T)) • l2Embed n Ω v₀)
    hy hv hyt hvt hd hdv yc (fun t : ℝ => (1 - t / T) • toL2L n Ω v₀) hyc hvc hyce
    (Eventually.of_forall fun t => by simp only [map_smul])
  have e3 : ∀ t : ℝ, ((-(1 / T)) • l2Embed n Ω v₀) (y t) = -(1 / T) * l2Embed n Ω v₀ (y t) := by
    intro t; simp only [one_div, neg_smul, neg_apply, smul_apply, smul_eq_mul, neg_mul]
  simp_rw [e3] at key
  rw [integral_const_mul] at key
  have e4 : (1 - T / T : ℝ) = 0 := by rw [div_self hT.ne']; ring
  simp only [e4, zero_smul, inner_zero_right, sub_zero, div_zero, zero_div, sub_self, one_smul] at key
  rw [key]; ring


end ibp
end HunterPDE.Parabolic
end Q0ffd_P3

section Q0ffd_P4
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section init
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}

lemma lam_abs_le (hT : 0 < T) : ∀ t ∈ Set.Ioo 0 T, |1 - t / T| ≤ 1 := by
  intro t ht
  have h1 : 0 < t / T := div_pos ht.1 hT
  have h2 : t / T < 1 := (div_lt_one hT).2 ht.2
  rw [abs_of_pos (by linarith)]; linarith

set_option maxHeartbeats 3200000 in
theorem limit_initial [IsFiniteMeasure (timeMeasure T)] [TopologicalSpace.SeparableSpace (H10 n Ω)]
    (hT : 0 < T) (hibp : IBPHyp n Ω T)
    {P : Coeffs n} (hP : P.Assumption61 Ω T)
    {f : ℝ → Hm1 n Ω} (hf : MemLp f 2 (timeMeasure T))
    {w : ℕ → H10 n Ω} {eig : ℕ → ℝ} (heig : IsDirichletEigenbasis Ω w eig)
    (g : Lp ℝ 2 (volume.restrict Ω))
    {u zl : ℝ → H10 n Ω} (hu : MemLp u 2 (timeMeasure T)) (hzl : MemLp zl 2 (timeMeasure T))
    (hweq : ∀ v : H10 n Ω, ∀ᵐ t ∂(timeMeasure T),
      dualL (H10 n Ω) (zl t) v + form P t (u t) v = f t v)
    (hd : HasWeakTimeDeriv (l2Embed n Ω) T u (fun t => dualL (H10 n Ω) (zl t)))
    {uc : ℝ → Lp ℝ 2 (volume.restrict Ω)} (hucc : ContinuousOn uc (Set.Icc 0 T))
    (huce : ∀ᵐ t ∂(timeMeasure T), uc t = toL2L n Ω (u t))
    {x y xc : ℕ → ℝ → H10 n Ω} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hx : ∀ k, MemLp (x k) 2 (timeMeasure T)) (hy : ∀ k, MemLp (y k) 2 (timeMeasure T))
    (hxy : ∀ k, HasWeakTimeDeriv (ContinuousLinearMap.id ℝ (H10 n Ω)) T (x k) (y k))
    (hGal : ∀ k, ∀ v ∈ galerkinSpace w (N k), ∀ᵐ t ∂(timeMeasure T),
      l2inner (y k t) v + form P t (x k t) v = f t v)
    (hxcc : ∀ k, ContinuousOn (xc k) (Set.Icc 0 T))
    (hxce : ∀ k, ∀ᵐ t ∂(timeMeasure T), xc k t = x k t)
    (hx0 : ∀ k, xc k 0 = galerkinProj w (N k) g)
    (hxc : ∀ Z : ℝ → H10 n Ω, MemLp Z 2 (timeMeasure T) →
      Tendsto (fun k => ∫ t, inner ℝ (Z t) (x k t) ∂(timeMeasure T)) atTop
        (𝓝 (∫ t, inner ℝ (Z t) (u t) ∂(timeMeasure T)))) :
    uc 0 = g := by
  have hob28 := form_time_regularity hP
  obtain ⟨-, hFint, hFconv⟩ := hob28
  have hcont : Continuous (fun t : ℝ => 1 - t / T) :=
    continuous_const.sub (continuous_id.div_const T)
  have hlamb := lam_abs_le hT
  have hlint : ∀ {g : ℝ → ℝ}, MemLp g 2 (timeMeasure T) →
      Integrable (fun t => (1 - t / T) * g t) (timeMeasure T) := by
    intro g hg
    have := MemLp.of_le_mul (c := 1) hg (hcont.measurable.aestronglyMeasurable.mul hg.1) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      show ‖(1 - t / T) * g t‖ ≤ 1 * ‖g t‖
      rw [norm_mul, Real.norm_eq_abs, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hlamb t ht))
    exact this.integrable (by norm_num)
  have hfv : ∀ v : H10 n Ω, MemLp (fun t => f t v) 2 (timeMeasure T) := by
    intro v
    convert comp_memLp_semi (E := Hm1 n Ω) (F := ℝ) (ContinuousLinearMap.apply ℝ ℝ v) hf <;> rfl
  have hw : MemLp (fun t => dualL (H10 n Ω) (zl t)) 2 (timeMeasure T) := by
    convert comp_memLp_semi (E := H10 n Ω) (F := Hm1 n Ω) (dualL (H10 n Ω)) hzl
  -- the main identity for v₀ in the Galerkin spaces
  have hmain : ∀ N0 : ℕ, ∀ v₀ ∈ galerkinSpace w N0,
      inner ℝ (uc 0) (toL2L n Ω v₀) = inner ℝ g (toL2L n Ω v₀) := by
    intro N0 v₀ hv₀
    have hform := hFint (ψ := fun t : ℝ => 1 - t / T) hcont.measurable
      (B := 1) zero_le_one hlamb v₀ hu
    -- (i) the limit
    have hi := ibp_lambda hT hibp hu hw hd hucc huce v₀
    have hi2 : ∫ t in Set.Ioo 0 T, dualL (H10 n Ω) (zl t) ((1 - t / T) • v₀) =
        ∫ t in Set.Ioo 0 T, (1 - t / T) * (f t v₀) - (1 - t / T) * form P t (u t) v₀ := by
      refine integral_congr_ae ?_
      filter_upwards [hweq v₀] with t ht
      rw [ContinuousLinearMap.map_smul, smul_eq_mul, ← mul_sub]
      congr 1
      exact eq_sub_of_add_eq ht
    rw [hi2, integral_sub (hlint (hfv v₀)) (hform)] at hi
    -- (ii) the Galerkin identities
    have hk : ∀ᶠ k in atTop,
        (∫ t in Set.Ioo 0 T, (1 - t / T) * (f t v₀)) -
          (∫ t in Set.Ioo 0 T, (1 - t / T) * form P t (x k t) v₀) =
        - inner ℝ (toL2L n Ω (galerkinProj w (N k) g)) (toL2L n Ω v₀) +
          (1 / T) * ∫ t in Set.Ioo 0 T, l2Embed n Ω v₀ (x k t) := by
      filter_upwards [hN.eventually_ge_atTop N0] with k hk
      have hvk : v₀ ∈ galerkinSpace w (N k) := galerkinSpace_mono w hk hv₀
      have hyl : MemLp (fun t => l2Embed n Ω (y k t)) 2 (timeMeasure T) := by
        convert comp_memLp_semi (E := H10 n Ω) (F := Hm1 n Ω) (l2Embed n Ω) (hy k)
      have hdk := galerkin_hwd_l2Embed T (x k) (y k) (hx k) (hy k) (hxy k)
      have hcc : ContinuousOn (fun t => toL2L n Ω (xc k t)) (Set.Icc 0 T) :=
        (toL2L n Ω).continuous.comp_continuousOn (hxcc k)
      have hce : ∀ᵐ t ∂(timeMeasure T), toL2L n Ω (xc k t) = toL2L n Ω (x k t) := by
        filter_upwards [hxce k] with t ht; rw [ht]
      have hik := ibp_lambda hT hibp (hx k) hyl hdk hcc hce v₀
      have hform' := hFint (ψ := fun t : ℝ => 1 - t / T) hcont.measurable
        (B := 1) zero_le_one hlamb v₀ (hx k)
      have e1 : ∫ t in Set.Ioo 0 T, l2Embed n Ω (y k t) ((1 - t / T) • v₀) =
          ∫ t in Set.Ioo 0 T, (1 - t / T) * (f t v₀) - (1 - t / T) * form P t (x k t) v₀ := by
        refine integral_congr_ae ?_
        filter_upwards [hGal k v₀ hvk] with t ht
        rw [ContinuousLinearMap.map_smul, smul_eq_mul, ← mul_sub, l2Embed_eq_l2inner]
        congr 1
        exact eq_sub_of_add_eq ht
      rw [e1, integral_sub (hlint (hfv v₀)) hform', hx0 k] at hik
      exact hik
    -- (iii) pass to the limit
    have hF := hFconv hcont.measurable zero_le_one hlamb v₀ hx hu hxc
    have hI : Tendsto (fun k => ∫ t in Set.Ioo 0 T, l2Embed n Ω v₀ (x k t)) atTop
        (𝓝 (∫ t in Set.Ioo 0 T, l2Embed n Ω v₀ (u t))) := by
      have := hxc (fun _ => rzL (H10 n Ω) (l2Embed n Ω v₀)) (memLp_const _)
      simp only [inner_rzL] at this
      exact this
    have hG : Tendsto (fun k => inner ℝ (toL2L n Ω (galerkinProj w (N k) g)) (toL2L n Ω v₀))
        atTop (𝓝 (inner ℝ g (toL2L n Ω v₀))) :=
      ((galerkinProj_tendsto heig g).comp hN).inner tendsto_const_nhds
    have hlim1 : Tendsto (fun k => (∫ t in Set.Ioo 0 T, (1 - t / T) * (f t v₀)) -
        (∫ t in Set.Ioo 0 T, (1 - t / T) * form P t (x k t) v₀)) atTop
        (𝓝 ((∫ t in Set.Ioo 0 T, (1 - t / T) * (f t v₀)) -
          (∫ t in Set.Ioo 0 T, (1 - t / T) * form P t (u t) v₀))) :=
      tendsto_const_nhds.sub hF
    have hlim2 : Tendsto (fun k => - inner ℝ (toL2L n Ω (galerkinProj w (N k) g)) (toL2L n Ω v₀) +
        (1 / T) * ∫ t in Set.Ioo 0 T, l2Embed n Ω v₀ (x k t)) atTop
        (𝓝 (- inner ℝ g (toL2L n Ω v₀) + (1 / T) * ∫ t in Set.Ioo 0 T, l2Embed n Ω v₀ (u t))) :=
      hG.neg.add (hI.const_mul _)
    have key := tendsto_nhds_unique_of_eventuallyEq hlim1 hlim2 hk
    linarith only [hi, key]
  -- (v) conclude
  have hperp : (Submodule.span ℝ (Set.range fun k => toL2 (w k))) ≤
      (Submodule.span ℝ {uc 0 - g})ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    have hwk : w k ∈ galerkinSpace w (k + 1) :=
      Submodule.subset_span ⟨k, by simp only [mem_Iio, lt_add_iff_pos_right, Order.lt_one_iff], rfl⟩
    have := hmain (k + 1) (w k) hwk
    rw [inner_sub_left, sub_eq_zero]
    exact this
  have hle := Submodule.topologicalClosure_minimal _ hperp (Submodule.isClosed_orthogonal _)
  rw [heig.2.2] at hle
  have hmem : uc 0 - g ∈ (Submodule.span ℝ {uc 0 - g})ᗮ := hle trivial
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hmem
  exact sub_eq_zero.1 (inner_self_eq_zero.1 hmem)

end init
end HunterPDE.Parabolic
end Q0ffd_P4

section Q0ffd_P5
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section est

/-- A bounded triple of nonnegative real sequences has a jointly convergent subsequence. -/
lemma subseq3 {a b c : ℕ → ℝ} {M : ℝ} (hs : ∀ k, a k + b k + c k ≤ M) (ha : ∀ k, 0 ≤ a k)
    (hb : ∀ k, 0 ≤ b k) (hc : ∀ k, 0 ≤ c k) :
    ∃ a0 b0 c0 : ℝ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun k => a (ψ k)) atTop (𝓝 a0) ∧
      Tendsto (fun k => b (ψ k)) atTop (𝓝 b0) ∧ Tendsto (fun k => c (ψ k)) atTop (𝓝 c0) ∧
      0 ≤ a0 ∧ 0 ≤ b0 ∧ 0 ≤ c0 ∧ a0 + b0 + c0 ≤ M := by
  obtain ⟨⟨a0, b0, c0⟩, -, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded
    (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ × ℝ)) (r := M))
    (x := fun k => (a k, b k, c k)) (fun k => by
      simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs]
      have h1 := hs k
      have h2 := ha k
      have h3 := hb k
      have h4 := hc k
      exact max_le (abs_le.2 ⟨by linarith, by linarith⟩)
        (max_le (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)))
  have hta : Tendsto (fun k => a (ψ k)) atTop (𝓝 a0) := (continuous_fst.tendsto _).comp hlim
  have htb : Tendsto (fun k => b (ψ k)) atTop (𝓝 b0) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have htc : Tendsto (fun k => c (ψ k)) atTop (𝓝 c0) :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hlim
  exact ⟨a0, b0, c0, ψ, hψ, hta, htb, htc, ge_of_tendsto' hta (fun k => ha _),
    ge_of_tendsto' htb (fun k => hb _), ge_of_tendsto' htc (fun k => hc _),
    le_of_tendsto_of_tendsto' ((hta.add htb).add htc) tendsto_const_nhds (fun k => hs (ψ k))⟩

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {T : ℝ}

set_option maxHeartbeats 1600000 in
/-- Weak lower semicontinuity of the three norms of the energy estimate (any `J : V →L H`). -/
theorem limit_estimate [IsFiniteMeasure (timeMeasure T)] (J : V →L[ℝ] H)
    {u zl : ℝ → V} (husm : StronglyMeasurable u) (hu : MemLp u 2 (timeMeasure T))
    (hzl : MemLp zl 2 (timeMeasure T))
    {x z : ℕ → ℝ → V}
    (hx : ∀ k, MemLp (x k) 2 (timeMeasure T)) (hz : ∀ k, MemLp (z k) 2 (timeMeasure T))
    (hxc : ∀ Z : ℝ → V, MemLp Z 2 (timeMeasure T) →
      Tendsto (fun k => ∫ t, inner ℝ (Z t) (x k t) ∂(timeMeasure T)) atTop
        (𝓝 (∫ t, inner ℝ (Z t) (u t) ∂(timeMeasure T))))
    (hzc : ∀ Z : ℝ → V, MemLp Z 2 (timeMeasure T) →
      Tendsto (fun k => ∫ t, inner ℝ (Z t) (z k t) ∂(timeMeasure T)) atTop
        (𝓝 (∫ t, inner ℝ (Z t) (zl t) ∂(timeMeasure T))))
    {Mtot : ℝ≥0∞} (hM : Mtot ≠ ⊤)
    (hb : ∀ k, eLpNorm (fun t => J (x k t)) ∞ (timeMeasure T) +
      eLpNorm (x k) 2 (timeMeasure T) + eLpNorm (z k) 2 (timeMeasure T) ≤ Mtot) :
    eLpNorm (fun t => J (u t)) ∞ (timeMeasure T) + eLpNorm u 2 (timeMeasure T) +
      eLpNorm zl 2 (timeMeasure T) ≤ Mtot := by
  have hfin1 : ∀ k, eLpNorm (fun t => J (x k t)) ∞ (timeMeasure T) ≠ ⊤ := fun k =>
    ne_top_of_le_ne_top hM ((le_self_add.trans le_self_add).trans (hb k))
  have hfin2 : ∀ k, eLpNorm (x k) 2 (timeMeasure T) ≠ ⊤ := fun k => (hx k).2.ne
  have hfin3 : ∀ k, eLpNorm (z k) 2 (timeMeasure T) ≠ ⊤ := fun k => (hz k).2.ne
  have hsum : ∀ k, (eLpNorm (fun t => J (x k t)) ∞ (timeMeasure T)).toReal +
      (eLpNorm (x k) 2 (timeMeasure T)).toReal + (eLpNorm (z k) 2 (timeMeasure T)).toReal ≤
      Mtot.toReal := by
    intro k
    have h := ENNReal.toReal_mono hM (hb k)
    rwa [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hfin1 k, hfin2 k⟩) (hfin3 k),
      ENNReal.toReal_add (hfin1 k) (hfin2 k)] at h
  have hob29 :=
    subseq3 hsum (fun k => ENNReal.toReal_nonneg) (fun k => ENNReal.toReal_nonneg)
      (fun k => ENNReal.toReal_nonneg)
  obtain ⟨a0, b0, c0, ψ, hψ, hta, htb, htc, ha0', hb0', hc0', hlimsum⟩ := hob29
  have hxc' : ∀ Z : ℝ → V, MemLp Z 2 (timeMeasure T) →
      Tendsto (fun k => ∫ t, inner ℝ (Z t) (x (ψ k) t) ∂(timeMeasure T)) atTop
        (𝓝 (∫ t, inner ℝ (Z t) (u t) ∂(timeMeasure T))) :=
    fun Z hZ => (hxc Z hZ).comp hψ.tendsto_atTop
  have hzc' : ∀ Z : ℝ → V, MemLp Z 2 (timeMeasure T) →
      Tendsto (fun k => ∫ t, inner ℝ (Z t) (z (ψ k) t) ∂(timeMeasure T)) atTop
        (𝓝 (∫ t, inner ℝ (Z t) (zl t) ∂(timeMeasure T))) :=
    fun Z hZ => (hzc Z hZ).comp hψ.tendsto_atTop
  -- the L^∞ part
  have hLinf : ∀ᵐ t ∂(timeMeasure T), ‖J (u t)‖ ≤ a0 := by
    refine linfty_bound J u husm hu (fun k => x (ψ k)) (fun k => hx _) hxc'
      (fun k => (eLpNorm (fun t => J (x (ψ k) t)) ∞ (timeMeasure T)).toReal) a0 ha0' hta
      (fun k => ?_)
    have h1 := ae_le_eLpNormEssSup (f := fun t => J (x (ψ k) t)) (μ := timeMeasure T)
    filter_upwards [h1] with t ht
    have h2 : ‖J (x (ψ k) t)‖ₑ ≤ eLpNorm (fun t => J (x (ψ k) t)) ∞ (timeMeasure T) := by
      rwa [eLpNorm_exponent_top]
    have h3 := ENNReal.toReal_mono (hfin1 (ψ k)) h2
    exact (toReal_enorm _).symm.le.trans h3
  have hA : eLpNorm (fun t => J (u t)) ∞ (timeMeasure T) ≤ ENNReal.ofReal a0 := by
    rw [eLpNorm_exponent_top]; exact eLpNormEssSup_le_of_ae_bound hLinf
  have hB : eLpNorm u 2 (timeMeasure T) ≤ ENNReal.ofReal b0 :=
    (ENNReal.le_ofReal_iff_toReal_le hu.2.ne hb0').2
      (eLpNorm_le_of_weak (fun k => hx (ψ k)) hu hxc' htb)
  have hC : eLpNorm zl 2 (timeMeasure T) ≤ ENNReal.ofReal c0 :=
    (ENNReal.le_ofReal_iff_toReal_le hzl.2.ne hc0').2
      (eLpNorm_le_of_weak (fun k => hz (ψ k)) hzl hzc' htc)
  calc _ ≤ ENNReal.ofReal a0 + ENNReal.ofReal b0 + ENNReal.ofReal c0 := by gcongr
    _ = ENNReal.ofReal (a0 + b0 + c0) := by
        rw [ENNReal.ofReal_add (add_nonneg ha0' hb0') hc0', ENNReal.ofReal_add ha0' hb0']
    _ ≤ ENNReal.ofReal Mtot.toReal := ENNReal.ofReal_le_ofReal hlimsum
    _ = Mtot := ENNReal.ofReal_toReal hM

end est
end HunterPDE.Parabolic
end Q0ffd_P5

section Q0ffd_A
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff
namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast
section asm

set_option maxHeartbeats 1600000 in
theorem galerkin_limit_of {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω)
    (T : ℝ) (hT : 0 < T) (P : Coeffs n) (hP : P.Assumption61 Ω T)
    (hen : ∃ C : ℝ≥0, ∀ (w : ℕ → H10 n Ω) (eig : ℕ → ℝ), IsDirichletEigenbasis Ω w eig →
      ∀ f : ℝ → Hm1 n Ω, MemLp f 2 (timeMeasure T) →
      ∀ (g : Lp ℝ 2 (volume.restrict Ω)) (N : ℕ) (uN uNt : ℝ → H10 n Ω),
        IsApproxSolution Ω T P w N f g uN uNt →
        eLpNorm (fun t => toL2 (uN t)) ∞ (timeMeasure T) + eLpNorm uN 2 (timeMeasure T) +
            eLpNorm (fun t => l2Embed n Ω (uNt t)) 2 (timeMeasure T) ≤
          (C : ℝ≥0∞) * (eLpNorm f 2 (timeMeasure T) + ‖g‖ₑ))
    (hhc : ∀ (u : ℝ → H10 n Ω) (ut : ℝ → Hm1 n Ω),
      MemLp u 2 (timeMeasure T) → MemLp ut 2 (timeMeasure T) →
      HasWeakTimeDeriv (l2Embed n Ω) T u ut →
      ∃ ũ : ℝ → Lp ℝ 2 (volume.restrict Ω), ContinuousOn ũ (Set.Icc 0 T) ∧
        ∀ᵐ t ∂(timeMeasure T), ũ t = toL2L n Ω (u t))
    (hibp : IBPHyp n Ω T) :
    ∃ C : ℝ≥0, ∀ (w : ℕ → H10 n Ω) (eig : ℕ → ℝ), IsDirichletEigenbasis Ω w eig →
      ∀ f : ℝ → Hm1 n Ω, MemLp f 2 (timeMeasure T) →
      ∀ (g : Lp ℝ 2 (volume.restrict Ω)) (uN uNt : ℕ → ℝ → H10 n Ω),
        (∀ N, IsApproxSolution Ω T P w N f g (uN N) (uNt N)) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (u : ℝ → H10 n Ω) (ut : ℝ → Hm1 n Ω),
          IsWeakSolution Ω T P f g u ut ∧
          (∀ F : ℝ → Hm1 n Ω, MemLp F 2 (timeMeasure T) →
            Tendsto (fun k => ∫ t in Set.Ioo 0 T, F t (uN (φ k) t)) atTop
              (𝓝 (∫ t in Set.Ioo 0 T, F t (u t)))) ∧
          (∀ v : ℝ → H10 n Ω, MemLp v 2 (timeMeasure T) →
            Tendsto (fun k => ∫ t in Set.Ioo 0 T, l2Embed n Ω (uNt (φ k) t) (v t)) atTop
              (𝓝 (∫ t in Set.Ioo 0 T, ut t (v t)))) ∧
          eLpNorm (fun t => toL2 (u t)) ∞ (timeMeasure T) + eLpNorm u 2 (timeMeasure T) +
              eLpNorm ut 2 (timeMeasure T) ≤
            (C : ℝ≥0∞) * (eLpNorm f 2 (timeMeasure T) + ‖g‖ₑ) := by
  have hfin : IsFiniteMeasure (timeMeasure T) :=
    isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  haveI : TopologicalSpace.SeparableSpace (H10 n Ω) := separable_H10
  obtain ⟨C, hC⟩ := hen
  refine ⟨C, ?_⟩
  intro w eig heig f hf g uN uNt happ
  let Mtot : ℝ≥0∞ := (C : ℝ≥0∞) * (eLpNorm f 2 (timeMeasure T) + ‖g‖ₑ)
  have hMfin : Mtot ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, enorm_ne_top⟩)
  have hb : ∀ N, eLpNorm (fun t => toL2 (uN N t)) ∞ (timeMeasure T) +
      eLpNorm (uN N) 2 (timeMeasure T) +
      eLpNorm (fun t => l2Embed n Ω (uNt N t)) 2 (timeMeasure T) ≤ Mtot :=
    fun N => hC w eig heig f hf g N (uN N) (uNt N) (happ N)
  have hx : ∀ N, MemLp (uN N) 2 (timeMeasure T) := fun N => (happ N).2.2.1
  have hy : ∀ N, MemLp (uNt N) 2 (timeMeasure T) := fun N => (happ N).2.2.2.1
  let z : ℕ → ℝ → H10 n Ω := fun k t => rzL (H10 n Ω) (l2Embed n Ω (uNt k t))
  have hz : ∀ k, MemLp (z k) 2 (timeMeasure T) := by
    intro k
    have h1 : MemLp (fun t => l2Embed n Ω (uNt k t)) 2 (timeMeasure T) := by
      convert comp_memLp_semi (E := H10 n Ω) (F := Hm1 n Ω) (l2Embed n Ω) (hy k)
    exact comp_memLp_semi (rzL (H10 n Ω)) h1
  have hzn : ∀ k, eLpNorm (z k) 2 (timeMeasure T) =
      eLpNorm (fun t => l2Embed n Ω (uNt k t)) 2 (timeMeasure T) := by
    intro k
    rw [el_norm (z k), el_norm (fun t => l2Embed n Ω (uNt k t))]
    simp only [z, norm_rzL]
  have hxb : ∀ k, (eLpNorm (uN k) 2 (timeMeasure T)).toReal ≤ Mtot.toReal := fun k =>
    ENNReal.toReal_mono hMfin (le_trans (le_trans le_add_self le_self_add) (hb k))
  have hzb : ∀ k, (eLpNorm (z k) 2 (timeMeasure T)).toReal ≤ Mtot.toReal := fun k => by
    rw [hzn k]; exact ENNReal.toReal_mono hMfin (le_trans le_add_self (hb k))
  have hob30 :=
    weak_subseq_fun (μ := timeMeasure T) uN hx Mtot.toReal hxb
  obtain ⟨φ1, hφ1, u, husm, hu, hxc1⟩ := hob30
  have hob31 :=
    weak_subseq_fun (μ := timeMeasure T) (fun k => z (φ1 k)) (fun k => hz _) Mtot.toReal
      (fun k => hzb (φ1 k))
  obtain ⟨φ2, hφ2, zl, -, hzl, hzc2⟩ := hob31
  have hφ : StrictMono (φ1 ∘ φ2) := hφ1.comp hφ2
  have hxc : ∀ Z : ℝ → H10 n Ω, MemLp Z 2 (timeMeasure T) →
      Tendsto (fun k => ∫ t, inner ℝ (Z t) (uN ((φ1 ∘ φ2) k) t) ∂(timeMeasure T)) atTop
        (𝓝 (∫ t, inner ℝ (Z t) (u t) ∂(timeMeasure T))) :=
    fun Z hZ => (hxc1 Z hZ).comp hφ2.tendsto_atTop
  have hzc : ∀ Z : ℝ → H10 n Ω, MemLp Z 2 (timeMeasure T) →
      Tendsto (fun k => ∫ t, inner ℝ (Z t)
        (rzL (H10 n Ω) (l2Embed n Ω (uNt ((φ1 ∘ φ2) k) t))) ∂(timeMeasure T)) atTop
        (𝓝 (∫ t, inner ℝ (Z t) (zl t) ∂(timeMeasure T))) :=
    fun Z hZ => hzc2 Z hZ
  have hx' : ∀ k, MemLp (uN ((φ1 ∘ φ2) k)) 2 (timeMeasure T) := fun k => hx _
  have hy' : ∀ k, MemLp (uNt ((φ1 ∘ φ2) k)) 2 (timeMeasure T) := fun k => hy _
  have hxy' : ∀ k, HasWeakTimeDeriv (ContinuousLinearMap.id ℝ (H10 n Ω)) T
      (uN ((φ1 ∘ φ2) k)) (uNt ((φ1 ∘ φ2) k)) := fun k => (happ _).2.2.2.2.1
  have hGal : ∀ k, ∀ v ∈ galerkinSpace w ((φ1 ∘ φ2) k), ∀ᵐ t ∂(timeMeasure T),
      l2inner (uNt ((φ1 ∘ φ2) k) t) v + form P t (uN ((φ1 ∘ φ2) k) t) v = f t v :=
    fun k => (happ _).2.2.2.2.2.1
  have hwtd : HasWeakTimeDeriv (l2Embed n Ω) T u (fun t => dualL (H10 n Ω) (zl t)) :=
    limit_hasWeakTimeDeriv hu hzl hx' hy' hxy' hxc hzc
  have hweq := limit_equation hP hf (toL2L_injective hΩo) heig hu hzl hφ.tendsto_atTop
    hx' hy' hGal hxc hzc
  have hut : MemLp (fun t => dualL (H10 n Ω) (zl t)) 2 (timeMeasure T) := by
    convert comp_memLp_semi (E := H10 n Ω) (F := Hm1 n Ω) (dualL (H10 n Ω)) hzl
  have hob32 := hhc u _ hu hut hwtd
  obtain ⟨uc, hucc, huce⟩ := hob32
  -- continuous representatives of the Galerkin approximations
  have hrep : ∀ k, ∃ ũ : ℝ → H10 n Ω, ContinuousOn ũ (Set.Icc 0 T) ∧
      (∀ᵐ t ∂(timeMeasure T), ũ t = uN ((φ1 ∘ φ2) k) t) ∧
      ũ 0 = galerkinProj w ((φ1 ∘ φ2) k) g := fun k => (happ _).2.2.2.2.2.2
  choose xc hxcc hxce hx0 using hrep
  have hinit : uc 0 = g :=
    limit_initial hT hibp hP hf heig g hu hzl hweq hwtd hucc huce hφ.tendsto_atTop hx' hy' hxy'
      hGal hxcc hxce hx0 hxc
  have hest := limit_estimate (toL2L n Ω) husm hu hzl (x := fun k => uN ((φ1 ∘ φ2) k))
    (z := fun k => z ((φ1 ∘ φ2) k)) hx' (fun k => hz _) hxc hzc hMfin
    (fun k => by
      have h := hb ((φ1 ∘ φ2) k)
      simp only [toL2_eq] at h
      rw [hzn]; exact h)
  have hutn : eLpNorm (fun t => dualL (H10 n Ω) (zl t)) 2 (timeMeasure T) =
      eLpNorm zl 2 (timeMeasure T) := by
    rw [el_norm (fun t => dualL (H10 n Ω) (zl t)), el_norm zl]
    simp only [norm_dualL]
  refine ⟨φ1 ∘ φ2, hφ, u, fun t => dualL (H10 n Ω) (zl t), ?_, ?_, ?_, ?_⟩
  · exact ⟨hu, hut, hwtd, hweq, uc, hucc, huce, hinit⟩
  · intro F hF
    have hZ : MemLp (fun t => rzL (H10 n Ω) (F t)) 2 (timeMeasure T) := by
      convert comp_memLp_semi (E := Hm1 n Ω) (F := H10 n Ω) (rzL (H10 n Ω)) hF <;> rfl
    have := hxc _ hZ
    simp only [inner_rzL] at this
    exact this
  · intro v hv
    have hpt : ∀ a b : H10 n Ω, inner ℝ b (rzL (H10 n Ω) (l2Embed n Ω a)) = l2Embed n Ω a b :=
      fun a b => by rw [real_inner_comm, inner_rzL]
    have hpt2 : ∀ a b : H10 n Ω, inner ℝ b a = dualL (H10 n Ω) a b :=
      fun a b => by rw [dualL_apply, real_inner_comm]
    have := hzc v hv
    simp only [hpt] at this
    simp only [hpt2] at this
    exact this
  · rw [hutn]
    simp only [toL2_eq]
    exact hest

end asm
end HunterPDE.Parabolic
end Q0ffd_A

open MeasureTheory Filter Topology HunterPDE.Parabolic in
open scoped ENNReal NNReal in
theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (P : Coeffs n)
    (hP : P.Assumption61 Ω T) :
    ∃ C : ℝ≥0, ∀ (w : ℕ → H10 n Ω) (eig : ℕ → ℝ), IsDirichletEigenbasis Ω w eig →
      ∀ f : ℝ → Hm1 n Ω, MemLp f 2 (timeMeasure T) →
      ∀ (g : Lp ℝ 2 (volume.restrict Ω)) (uN uNt : ℕ → ℝ → H10 n Ω),
        (∀ N, IsApproxSolution Ω T P w N f g (uN N) (uNt N)) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (u : ℝ → H10 n Ω) (ut : ℝ → Hm1 n Ω),
          IsWeakSolution Ω T P f g u ut ∧
          (∀ F : ℝ → Hm1 n Ω, MemLp F 2 (timeMeasure T) →
            Tendsto (fun k => ∫ t in Set.Ioo 0 T, F t (uN (φ k) t)) atTop
              (𝓝 (∫ t in Set.Ioo 0 T, F t (u t)))) ∧
          (∀ v : ℝ → H10 n Ω, MemLp v 2 (timeMeasure T) →
            Tendsto (fun k => ∫ t in Set.Ioo 0 T, l2Embed n Ω (uNt (φ k) t) (v t)) atTop
              (𝓝 (∫ t in Set.Ioo 0 T, ut t (v t)))) ∧
          eLpNorm (fun t => toL2 (u t)) ∞ (timeMeasure T) + eLpNorm u 2 (timeMeasure T) +
              eLpNorm ut 2 (timeMeasure T) ≤
            (C : ℝ≥0∞) * (eLpNorm f 2 (timeMeasure T) + ‖g‖ₑ) := by
  have hibp : IBPHyp n Ω T := fun u v ut vt hu hv hut hvt hdu hdv uc vc hucc hvcc huc hvc =>
    integration_by_parts (h10Triple hΩo) T hT u v ut vt hu hv hut hvt hdu hdv uc vc hucc hvcc
      huc hvc
  have hob33 := hilbert_triple_continuity (h10Triple hΩo) T hT
  obtain ⟨Ch, hCh⟩ := hob33
  exact galerkin_limit_of Ω hΩo T hT P hP (galerkin_energy_estimate Ω hΩo hΩb T hT P hP)
    (fun u ut hu hut hd => by
      have hob34 := hCh u ut hu hut hd
      obtain ⟨uc, h1, h2, -⟩ := hob34
      exact ⟨uc, h1, h2⟩) hibp
