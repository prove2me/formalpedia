-- Prove2me | solution 1 for OAI.SmoothLocal.HighEquation.exists_actual_comparison_energy
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:55:15.518201+00:00
-- url     : https://prove2.me/submissions/c010ddcd-1665-4f89-ad76-9fcd69f1b24c

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport
import Theorems.Thm_OAI_SmoothLocal_HighEquation_comparison_initial_energy_zero

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators
open Filter

namespace SmoothLocal.Geometry

section Height
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {F : Coord → V} {p : Coord} {U : Set Coord}

theorem partial_contDiffOn (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (i : Fin 2) :
    ContDiffOn ℝ ∞ (coordPartial i F) U := by
  exact (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

end Height
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology Interval ContDiff

namespace SmoothLocal.ODE

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem hasDerivAt_continuousMap_of_eval
    {a b : ℝ} {F P : ℝ → C(X, E)}
    (hP : ContinuousOn P (Ioo a b))
    (hpoint : ∀ t ∈ Ioo a b, ∀ x : X,
      HasDerivAt (fun s => F s x) (P t x) t)
    {t : ℝ} (ht : t ∈ Ioo a b) : HasDerivAt F (P t) t := by
  have hmeas : StronglyMeasurableAtFilter P (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hP t ht
  have hprim : HasDerivAt (fun y => F t + ∫ s in t..y, P s) (P t) t :=
    (intervalIntegral.integral_hasDerivAt_right
      (IntervalIntegrable.refl : IntervalIntegrable P volume t t)
      hmeas (hP.continuousAt (Ioo_mem_nhds ht.1 ht.2))).const_add (F t)
  have heq : F =ᶠ[𝓝 t] (fun y => F t + ∫ s in t..y, P s) := by
    apply Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2)
    intro y hy
    have hseg : uIcc t y ⊆ Ioo a b := by
      intro s hs
      exact ⟨lt_of_lt_of_le (lt_min ht.1 hy.1) hs.1,
        lt_of_le_of_lt hs.2 (max_lt ht.2 hy.2)⟩
    have hPI : IntervalIntegrable P volume t y := (hP.mono hseg).intervalIntegrable
    apply ContinuousMap.ext
    intro x
    have hPIx : IntervalIntegrable (fun s => P s x) volume t y :=
      ((ContinuousMap.evalCLM ℝ x).continuous.comp_continuousOn
        (hP.mono hseg)).intervalIntegrable
    have hscalar : (∫ s in t..y, P s x) = F y x - F t x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hpoint s (hseg hs) x) hPIx
    change F y x = F t x + (ContinuousMap.evalCLM ℝ x) (∫ s in t..y, P s)
    rw [← (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm hPI]
    change F y x = F t x + ∫ s in t..y, P s x
    rw [hscalar]
    abel
  exact hprim.congr_of_eventuallyEq heq

theorem continuousMap_smooth_of_eval_derivative_sequence
    {a b : ℝ} (F : ℕ → ℝ → C(X, E))
    (hcont : ∀ n, ContinuousOn (F n) (Ioo a b))
    (hpoint : ∀ n t, t ∈ Ioo a b → ∀ x : X,
      HasDerivAt (fun s => F n s x) (F (n + 1) t x) t) :
    ∀ n, ContDiffOn ℝ ∞ (F n) (Ioo a b) := by
  have hd (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (F n) (F (n + 1) t) t :=
    hasDerivAt_continuousMap_of_eval (hcont (n + 1)) (hpoint n) ht
  have hnat : ∀ m : ℕ, ∀ n : ℕ, ContDiffOn ℝ m (F n) (Ioo a b) := by
    intro m
    induction m with
    | zero =>
        intro n
        simpa only [Nat.cast_zero, contDiffOn_zero] using hcont n
    | succ m hm =>
        intro n
        have hnext : ContDiffOn ℝ ((m : ℕ∞ω) + 1) (F n) (Ioo a b) := by
          rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
          refine ⟨fun t ht => (hd n t ht).differentiableAt.differentiableWithinAt,
            by simp, ?_⟩
          exact (hm (n + 1)).congr (fun t ht => (hd n t ht).deriv)
        simpa only [Nat.cast_add, Nat.cast_one] using hnext
  intro n
  exact contDiffOn_infty.mpr (fun m => hnat m n)

theorem smooth_curry_of_joint_derivative_sequence
    {a b : ℝ} (H : ℕ → ℝ → X → E)
    (hjoint : ∀ n, ContinuousOn (Function.uncurry (H n))
      ((Ioo a b) ×ˢ (Set.univ : Set X)))
    (hpoint : ∀ n t, t ∈ Ioo a b → ∀ x : X,
      HasDerivAt (fun s => H n s x) (H (n + 1) t x) t) :
    ∀ n, ContDiffOn ℝ ∞ (fun t => ContinuousMap.mkD (H n t) 0) (Ioo a b) := by
  let F : ℕ → ℝ → C(X, E) := fun n t => ContinuousMap.mkD (H n t) 0
  have hslice (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) : Continuous (H n t) :=
    (hjoint n).comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨ht, Set.mem_univ _⟩)
  have heval (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : X) : F n t x = H n t x := by
    dsimp only [F]
    rw [ContinuousMap.mkD_of_continuous (hslice n t ht)]
    rfl
  have hcont (n : ℕ) : ContinuousOn (F n) (Ioo a b) :=
    ContinuousMap.continuousOn_mkD_of_uncurry (H n) 0 (hjoint n)
  have hpointF (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : X) :
      HasDerivAt (fun s => F n s x) (F (n + 1) t x) t := by
    have hevent : (fun s => F n s x) =ᶠ[𝓝 t] (fun s => H n s x) :=
      Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2)
        (fun s hs => heval n s hs x)
    rw [heval (n + 1) t ht x]
    exact (hpoint n t ht x).congr_of_eventuallyEq hevent
  exact continuousMap_smooth_of_eval_derivative_sequence F hcont hpointF

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology Interval

namespace SmoothLocal.ODE

abbrev IntervalFunctions (r : ℝ) := C(Icc (-r) r, ℝ)

def intervalExtension (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) : C(ℝ, ℝ) :=
  letI : Fact (-r ≤ r) := ⟨by linarith⟩
  ContinuousMap.IccExtendCM h

theorem intervalExtension_apply_of_mem (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) {x : ℝ} (hx : x ∈ Icc (-r) r) :
    intervalExtension r hr h x = h ⟨x, hx⟩ := by
  let : Fact (-r ≤ r) := ⟨by linarith⟩
  exact ContinuousMap.IccExtendCM_of_mem hx

theorem intervalExtension_norm_le (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : ℝ) :
    ‖intervalExtension r hr h x‖ ≤ ‖h‖ := by
  exact h.norm_coe_le_norm _

@[simp]
theorem intervalExtension_add (r : ℝ) (hr : 0 < r)
    (h k : IntervalFunctions r) (x : ℝ) :
    intervalExtension r hr (h + k) x =
      intervalExtension r hr h x + intervalExtension r hr k x := rfl

@[simp]
theorem intervalExtension_smul (r : ℝ) (hr : 0 < r)
    (c : ℝ) (h : IntervalFunctions r) (x : ℝ) :
    intervalExtension r hr (c • h) x = c • intervalExtension r hr h x := rfl

def primitiveFunction (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) (x : ℝ) : ℝ :=
  ∫ t in 0..x, intervalExtension r hr h t

theorem primitiveFunction_continuous (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) : Continuous (primitiveFunction r hr h) :=
  (intervalIntegral.differentiable_integral_of_continuous
    (intervalExtension r hr h).continuous).continuous

theorem primitiveFunction_hasDerivAt (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : ℝ) :
    HasDerivAt (primitiveFunction r hr h) (intervalExtension r hr h x) x :=
  intervalIntegral.integral_hasDerivAt_right
    ((intervalExtension r hr h).continuous.intervalIntegrable 0 x)
    ((intervalExtension r hr h).continuous.stronglyMeasurableAtFilter volume (𝓝 x))
    (intervalExtension r hr h).continuous.continuousAt

def primitiveMap (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) : IntervalFunctions r :=
  ⟨fun x => primitiveFunction r hr h x,
    (primitiveFunction_continuous r hr h).comp continuous_subtype_val⟩

@[simp]
theorem primitiveMap_apply (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : Icc (-r) r) :
    primitiveMap r hr h x = ∫ t in 0..(x : ℝ), intervalExtension r hr h t := rfl

def primitiveLinearMap (r : ℝ) (hr : 0 < r) :
    IntervalFunctions r →ₗ[ℝ] IntervalFunctions r where
  toFun := primitiveMap r hr
  map_add' h k := by
    apply ContinuousMap.ext
    intro x
    change (∫ t in 0..(x : ℝ), intervalExtension r hr (h + k) t) =
      (∫ t in 0..(x : ℝ), intervalExtension r hr h t) +
      (∫ t in 0..(x : ℝ), intervalExtension r hr k t)
    simp only [intervalExtension_add]
    exact intervalIntegral.integral_add
      ((intervalExtension r hr h).continuous.intervalIntegrable 0 x)
      ((intervalExtension r hr k).continuous.intervalIntegrable 0 x)
  map_smul' c h := by
    apply ContinuousMap.ext
    intro x
    change (∫ t in 0..(x : ℝ), intervalExtension r hr (c • h) t) =
      c • (∫ t in 0..(x : ℝ), intervalExtension r hr h t)
    simp only [intervalExtension_smul]
    exact intervalIntegral.integral_smul c (fun t => intervalExtension r hr h t)

theorem primitiveMap_norm_le (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) :
    ‖primitiveMap r hr h‖ ≤ r * ‖h‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hr.le (norm_nonneg h))).mpr
  intro x
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := (x : ℝ)) (C := ‖h‖)
    (f := fun t => intervalExtension r hr h t)
    (fun t _ => intervalExtension_norm_le r hr h t)
  have hx : |(x : ℝ)| ≤ r := abs_le.mpr x.2
  change ‖∫ t in 0..(x : ℝ), intervalExtension r hr h t‖ ≤ r * ‖h‖
  calc
    ‖∫ t in 0..(x : ℝ), intervalExtension r hr h t‖ ≤ ‖h‖ * |(x : ℝ)| := by
      simpa only [sub_zero] using hi
    _ ≤ ‖h‖ * r := mul_le_mul_of_nonneg_left hx (norm_nonneg h)
    _ = r * ‖h‖ := mul_comm _ _

def primitiveCLM (r : ℝ) (hr : 0 < r) :
    IntervalFunctions r →L[ℝ] IntervalFunctions r :=
  (primitiveLinearMap r hr).mkContinuous r (primitiveMap_norm_le r hr)

@[simp]
theorem primitiveCLM_apply (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : Icc (-r) r) :
    primitiveCLM r hr h x = ∫ t in 0..(x : ℝ), intervalExtension r hr h t := rfl

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

def jointDifferential (fx fy : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight fx +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight fy

theorem jointDifferential_eq_coprod (fx fy : ℝ) :
    jointDifferential fx fy =
      (ContinuousLinearMap.toSpanSingleton ℝ fx).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ fy) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [jointDifferential]

theorem hasFDerivAt_of_continuous_partials
    {s : Set (ℝ × ℝ)} (hs : IsOpen s) {f fx fy : (ℝ × ℝ) → ℝ}
    (hcx : ContinuousOn fx s) (hcy : ContinuousOn fy s)
    (hdx : ∀ p ∈ s, HasDerivAt (fun x => f (x, p.2)) (fx p) p.1)
    (hdy : ∀ p ∈ s, HasDerivAt (fun y => f (p.1, y)) (fy p) p.2)
    {p : ℝ × ℝ} (hp : p ∈ s) :
    HasFDerivAt f (jointDifferential (fx p) (fy p)) p := by
  have hspan : Continuous (ContinuousLinearMap.toSpanSingleton ℝ :
      ℝ → (ℝ →L[ℝ] ℝ)) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous
  have hfirst : ∀ᶠ q in 𝓝 p,
      HasFDerivAt (fun x => f (x, q.2))
        (ContinuousLinearMap.toSpanSingleton ℝ (fx q)) q.1 := by
    filter_upwards [hs.mem_nhds hp] with q hq
    exact (hdx q hq).hasFDerivAt
  have hsecond : ∀ᶠ q in 𝓝 p,
      HasFDerivAt (fun y => f (q.1, y))
        (ContinuousLinearMap.toSpanSingleton ℝ (fy q)) q.2 := by
    filter_upwards [hs.mem_nhds hp] with q hq
    exact (hdy q hq).hasFDerivAt
  have hfull := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ)
    (f := fun x y => f (x, y))
    (f₁ := fun x y => ContinuousLinearMap.toSpanSingleton ℝ (fx (x, y)))
    (f₂ := fun x y => ContinuousLinearMap.toSpanSingleton ℝ (fy (x, y)))
    hfirst hsecond
    (hspan.continuousAt.comp (hcx.continuousAt (hs.mem_nhds hp)))
    (hspan.continuousAt.comp (hcy.continuousAt (hs.mem_nhds hp)))
  rw [jointDifferential_eq_coprod]
  exact hfull.hasFDerivAt

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace SmoothLocal.Hyperbolic

theorem integral_square_eq_L2_norm_square
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : (∫ x, f x ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  calc
    (∫ x, f x ^ 2 ∂μ) = ∫ x, inner ℝ (hf.toLp f x) (hf.toLp f x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := rfl
    _ = ‖hf.toLp f‖ ^ 2 := real_inner_self_eq_norm_sq _

theorem sqrt_integral_square_eq_L2_norm
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : Real.sqrt (∫ x, f x ^ 2 ∂μ) = ‖hf.toLp f‖ := by
  rw [integral_square_eq_L2_norm_square hf, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem integral_product_abs_le_sqrt_squares
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have he : (∫ x, f x * g x ∂μ) = inner ℝ (hf.toLp f) (hg.toLp g) := by
    change (∫ x, f x * g x ∂μ) = ∫ x, inner ℝ (hf.toLp f x) (hg.toLp g x) ∂μ
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    simp only [hfx, hgx, Real.inner_apply]
  rw [he, sqrt_integral_square_eq_L2_norm hf, sqrt_integral_square_eq_L2_norm hg]
  exact abs_real_inner_le_norm _ _

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter
namespace SmoothLocal.Geometry

section Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {F : Coord → V} {U : Set Coord} {p : Coord}

theorem second_coordPartial_eq_fderiv (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j F) p =
      fderiv ℝ (fderiv ℝ F) p (Pi.single i 1) (Pi.single j 1) := by
  have hs : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hs p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  unfold coordPartial
  rw [fderiv_clm_apply hd (differentiableAt_const (c := Pi.single j (1 : ℝ)))]
  simp

theorem coordPartial_comm (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j F) p = coordPartial j (coordPartial i F) p := by
  rw [second_coordPartial_eq_fderiv hF hU hp, second_coordPartial_eq_fderiv hF hU hp]
  exact (((hF p hp).contDiffAt (hU.mem_nhds hp)).isSymmSndFDerivAt
    (by
      simp only [minSmoothness, ite_eq_left (inferInstance : IsRCLikeNormedField ℝ)]
      exact WithTop.coe_le_coe.mpr le_top)) _ _

end Calculus

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix

namespace SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord}

theorem metricDet_ne_zero (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) :
    (g p).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 p hp).isUnit).ne_zero

theorem metricDet_contDiffOn (hg : SmoothPositiveOn g U) :
    ContDiffOn ℝ ∞ (fun p => (g p).det) U := by
  simpa only [Matrix.det_fin_two] using
    ((hg.1 0 0).mul (hg.1 1 1)).sub ((hg.1 0 1).mul (hg.1 1 0))

theorem metricAdjugate_contDiffOn (hg : SmoothPositiveOn g U) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => (g p).adjugate i j) U := by
  fin_cases i <;> fin_cases j
  · simpa [Matrix.adjugate_fin_two] using hg.1 1 1
  · simpa [Matrix.adjugate_fin_two] using (hg.1 0 1).neg
  · simpa [Matrix.adjugate_fin_two] using (hg.1 1 0).neg
  · simpa [Matrix.adjugate_fin_two] using hg.1 0 0

theorem inverseMetric_contDiffOn (hg : SmoothPositiveOn g U) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => inverseMetric g p i j) U := by
  have hi : ContDiffOn ℝ ∞ (fun p => ((g p).det)⁻¹) U :=
    (metricDet_contDiffOn hg).inv (fun p hp => metricDet_ne_zero hg hp)
  have ha := metricAdjugate_contDiffOn hg i j
  simpa [inverseMetric, Matrix.inv_def, Ring.inverse_eq_inv, smul_eq_mul] using hi.mul ha

theorem christoffel_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (k i j : Fin 2) :
    ContDiffOn ℝ ∞ (christoffel g k i j) U := by
  have hs : ContDiffOn ℝ ∞ (fun p => ∑ l, inverseMetric g p k l *
      (coordPartial i (fun q => g q j l) p +
        coordPartial j (fun q => g q i l) p -
        coordPartial l (fun q => g q i j) p)) U := by
    apply ContDiffOn.sum
    intro l hl
    exact (inverseMetric_contDiffOn hg k l).mul
      (((partial_contDiffOn (hg.1 j l) hU i).add
        (partial_contDiffOn (hg.1 i l) hU j)).sub
        (partial_contDiffOn (hg.1 i j) hU l))
  exact contDiffOn_const.mul hs

theorem covHessian_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    {z : Coord → ℝ} (hz : ContDiffOn ℝ ∞ z U) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => covHessian g z p i j) U := by
  have hs : ContDiffOn ℝ ∞ (fun p => ∑ k,
      christoffel g k i j p * coordPartial k z p) U := by
    apply ContDiffOn.sum
    intro k hk
    exact (christoffel_contDiffOn hg hU k i j).mul (partial_contDiffOn hz hU k)
  exact (partial_contDiffOn (partial_contDiffOn hz hU j) hU i).sub hs

theorem riemann_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (l k i j : Fin 2) :
    ContDiffOn ℝ ∞ (riemann g l k i j) U := by
  have hs : ContDiffOn ℝ ∞ (fun p => ∑ m,
      (christoffel g m j k p * christoffel g l i m p -
        christoffel g m i k p * christoffel g l j m p)) U := by
    apply ContDiffOn.sum
    intro m hm
    exact ((christoffel_contDiffOn hg hU m j k).mul
      (christoffel_contDiffOn hg hU l i m)).sub
        ((christoffel_contDiffOn hg hU m i k).mul
          (christoffel_contDiffOn hg hU l j m))
  exact ((partial_contDiffOn (christoffel_contDiffOn hg hU l j k) hU i).sub
    (partial_contDiffOn (christoffel_contDiffOn hg hU l i k) hU j)).add hs

theorem gaussianCurvature_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (gaussianCurvature g) U := by
  have hn : ContDiffOn ℝ ∞ (fun p => ∑ l, g p 0 l * riemann g l 1 0 1 p) U := by
    apply ContDiffOn.sum
    intro l hl
    exact (hg.1 0 l).mul (riemann_contDiffOn hg hU l 1 0 1)
  exact hn.div (metricDet_contDiffOn hg) (fun p hp => metricDet_ne_zero hg hp)

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

theorem coordinatePoint_hasDerivAt_y (x y : ℝ) :
    HasDerivAt (coordinatePoint x) (Pi.single 1 (1 : ℝ) : Coord) y := by
  change HasDerivAt (fun t : ℝ => x • (Pi.single 0 (1 : ℝ) : Coord) +
    t • (Pi.single 1 (1 : ℝ) : Coord)) (Pi.single 1 (1 : ℝ) : Coord) y
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id y).smul_const (Pi.single 1 (1 : ℝ) : Coord)).const_add
      (x • (Pi.single 0 (1 : ℝ) : Coord))

def curvatureYDerivative (K : Coord → ℝ) : ℕ → Coord → ℝ
  | 0 => K
  | n + 1 => coordPartial 1 (curvatureYDerivative K n)

def coordinateCurvatureFamily (K : Coord → ℝ) (r : ℝ) (y : ℝ) : IntervalFunctions r :=
  ContinuousMap.mkD (fun x : Icc (-r) r => K (coordinatePoint x y)) 0

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
namespace SmoothLocal.Geometry

theorem SmoothPositiveOn.mono {g : MetricField} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hVU : V ⊆ U) : SmoothPositiveOn g V :=
  ⟨fun i j => (hg.1 i j).mono hVU,fun p hp => hg.2 p (hVU hp)⟩

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix
namespace SmoothLocal.Geometry

def christoffelFirstKind (g : MetricField) (i j : Fin 2) (p : Coord) : Coord :=
  fun l => (coordPartial i (fun q => g q j l) p +
    coordPartial j (fun q => g q i l) p - coordPartial l (fun q => g q i j) p) / 2

theorem christoffel_eq_inverse_mulVec (g : MetricField) (i j : Fin 2) (p : Coord) :
    (fun k => christoffel g k i j p) = (g p)⁻¹ *ᵥ christoffelFirstKind g i j p := by
  ext k
  simp only [christoffel, inverseMetric, Matrix.mulVec, dotProduct, christoffelFirstKind]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem metric_mul_christoffel {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) (i j : Fin 2) :
    g p *ᵥ (fun k => christoffel g k i j p) = christoffelFirstKind g i j p := by
  rw [christoffel_eq_inverse_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 p hp).isUnit),
    Matrix.one_mulVec]

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

theorem affineCoordinates_contDiff (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiff ℝ ∞ (affineCoordinates b R) :=
  contDiff_const.add (matrixContinuousLinear R).contDiff

theorem affineCoordinates_hasFDerivAt (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (q : Coord) : HasFDerivAt (affineCoordinates b R) (matrixContinuousLinear R) q := by
  change HasFDerivAt (fun x => b + matrixContinuousLinear R x)
    (matrixContinuousLinear R) q
  exact (matrixContinuousLinear R).hasFDerivAt.const_add b

theorem affineCoordinates_fderiv (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (q : Coord) : fderiv ℝ (affineCoordinates b R) q = matrixContinuousLinear R :=
  (affineCoordinates_hasFDerivAt b R q).fderiv

@[simp] theorem affineCoordinates_zero (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    affineCoordinates b R 0 = b := by simp [affineCoordinates]

theorem isOpen_affine_preimage {U : Set Coord} (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    IsOpen (affineCoordinates b R ⁻¹' U) :=
  hU.preimage (affineCoordinates_contDiff b R).continuous

theorem affine_comp_contDiffOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiffOn ℝ ∞ (f ∘ affineCoordinates b R) (affineCoordinates b R ⁻¹' U) :=
  hf.comp (affineCoordinates_contDiff b R).contDiffOn (fun _ hq => hq)

theorem fderiv_affine_comp_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q v : Coord)
    (hf : DifferentiableAt ℝ f (affineCoordinates b R q)) :
    fderiv ℝ (f ∘ affineCoordinates b R) q v =
      fderiv ℝ f (affineCoordinates b R q) (R *ᵥ v) := by
  rw [fderiv_comp q hf (affineCoordinates_hasFDerivAt b R q).differentiableAt,
    affineCoordinates_fderiv, ContinuousLinearMap.comp_apply, matrixContinuousLinear_apply]

theorem affinePullbackMetric_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : Function.Injective R.mulVec) :
    SmoothPositiveOn (affinePullbackMetric g b R) (affineCoordinates b R ⁻¹' U) := by
  constructor
  · intro i j
    have hc (a k : Fin 2) : ContDiffOn ℝ ∞
        (fun q => g (affineCoordinates b R q) a k) (affineCoordinates b R ⁻¹' U) :=
      affine_comp_contDiffOn (hg.1 a k) b R
    simp only [affinePullbackMetric, Matrix.mul_apply, Matrix.transpose_apply]
    apply ContDiffOn.sum
    intro k _
    apply ContDiffOn.mul _ contDiffOn_const
    apply ContDiffOn.sum
    intro a _
    exact contDiffOn_const.mul (hc a k)
  · intro q hq
    simpa only [affinePullbackMetric, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hg.2 (affineCoordinates b R q) hq).conjTranspose_mul_mul_same hR

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace HessianCalculus

variable {f h : Coord → ℝ} {p : Coord}

theorem coordPartial_add_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q + h q) p = coordPartial i f p + coordPartial i h p := by
  simp [coordPartial, fderiv_fun_add hf hh]

theorem coordPartial_sub_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q - h q) p = coordPartial i f p - coordPartial i h p := by
  simp [coordPartial, fderiv_fun_sub hf hh]

theorem coordPartial_mul_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q * h q) p =
      coordPartial i f p * h p + f p * coordPartial i h p := by
  simp [coordPartial, fderiv_fun_mul hf hh, add_comm, mul_comm]

theorem coordPartial_sum_two (f : Fin 2 → Coord → ℝ)
    (hf : ∀ a, DifferentiableAt ℝ (f a) p) (i : Fin 2) :
    coordPartial i (fun q => ∑ a, f a q) p = ∑ a, coordPartial i (f a) p := by
  simp only [Fin.sum_univ_two]
  exact coordPartial_add_at (hf 0) (hf 1) i

end HessianCalculus

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem metric_coeff_symm (hg : SmoothPositiveOn g U) (hp : p ∈ U) (i j : Fin 2) :
    g p i j = g p j i := by
  simpa using (hg.2 p hp).1.apply j i

theorem metric_coeff_partial_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k i j : Fin 2) :
    coordPartial k (fun q => g q i j) p = coordPartial k (fun q => g q j i) p := by
  have heq : (fun q => g q i j) =ᶠ[𝓝 p] (fun q => g q j i) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact metric_coeff_symm hg hq i j
  unfold coordPartial
  rw [heq.fderiv_eq]

theorem christoffel_lower_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k i j : Fin 2) :
    christoffel g k i j p = christoffel g k j i p := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [metric_coeff_partial_symm hg hU hp l i j]
  ring

theorem covHessian_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (i j : Fin 2) :
    covHessian g z p i j = covHessian g z p j i := by
  unfold covHessian
  rw [coordPartial_comm hz hU hp i j]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [christoffel_lower_symm hg hU hp a i j]

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

def intervalExtensionEvalCLM (r : ℝ) (hr : 0 < r) (x : ℝ) :
    IntervalFunctions r →L[ℝ] ℝ :=
  letI : Fact (-r ≤ r) := ⟨by linarith⟩
  ContinuousMap.evalCLM ℝ (ContinuousMap.projIccCM (a := -r) (b := r) x)

theorem intervalExtension_family_continuousOn (r : ℝ) (hr : 0 < r)
    {s : Set ℝ} {F : ℝ → IntervalFunctions r} (hF : ContinuousOn F s) :
    ContinuousOn (fun p : ℝ × ℝ => intervalExtension r hr (F p.2) p.1)
      (univ ×ˢ s) := by
  let : Fact (-r ≤ r) := ⟨by linarith⟩
  have hext : ContinuousOn (fun y => intervalExtension r hr (F y)) s :=
    ContinuousMap.IccExtendCM.continuous.comp_continuousOn hF
  exact (hext.comp continuous_snd.continuousOn (fun _ hp => hp.2)).eval
    continuous_fst.continuousOn

theorem intervalExtension_family_hasDerivAt (r : ℝ) (hr : 0 < r)
    {F : ℝ → IntervalFunctions r} {F' : IntervalFunctions r} {y : ℝ}
    (hF : HasDerivAt F F' y) (x : ℝ) :
    HasDerivAt (fun t => intervalExtension r hr (F t) x)
      (intervalExtension r hr F' x) y := by
  exact (intervalExtensionEvalCLM r hr x).hasFDerivAt.comp_hasDerivAt y hF

theorem intervalExtension_primitive_hasDerivAt (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) {x : ℝ} (hx : x ∈ Ioo (-r) r) :
    HasDerivAt (fun t => intervalExtension r hr (primitiveCLM r hr h) t)
      (intervalExtension r hr h x) x := by
  apply (primitiveFunction_hasDerivAt r hr h x).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  rw [intervalExtension_apply_of_mem r hr _ ⟨ht.1.le, ht.2.le⟩]
  rfl

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix
namespace SmoothLocal.Geometry

theorem heightEnergy_polynomial {g : MetricField} (z : Coord → ℝ) {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) :
    heightEnergy g z p = (g p).det -
      (g p 1 1 * (coordPartial 0 z p) ^ 2 -
        (g p 0 1 + g p 1 0) * coordPartial 0 z p * coordPartial 1 z p +
        g p 0 0 * (coordPartial 1 z p) ^ 2) := by
  have hdet := metricDet_ne_zero hg hp
  simp only [heightEnergy, covectorNormSq, inverseMetric, Matrix.inv_def,
    Ring.inverse_eq_inv, Matrix.adjugate_fin_two, Fin.sum_univ_two]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hdet]
  ring

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

theorem iteratedDeriv_contDiffOn_of_isOpen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} (hs : IsOpen s) {F : ℝ → E} (hF : ContDiffOn ℝ ∞ F s) :
    ∀ n, ContDiffOn ℝ ∞ (iteratedDeriv n F) s := by
  intro n
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hF
  | succ n hn =>
      rw [iteratedDeriv_succ]
      exact hn.deriv_of_isOpen hs (by simp)

theorem iteratedDeriv_clm_comp
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {f : ℝ → E} {y : ℝ} (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f y) :
    iteratedDeriv n (fun t => L (f t)) y = L (iteratedDeriv n f y) := by
  change iteratedFDeriv ℝ n (L ∘ f) y (fun _ => 1) = _
  rw [L.iteratedFDeriv_comp_left hf (WithTop.coe_le_coe.mpr le_top)]
  rfl

def intervalFamilyJet (r : ℝ) (hr : 0 < r)
    (F : ℝ → IntervalFunctions r) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  intervalExtension r hr (iteratedDeriv n F p.2) p.1

theorem intervalFamilyJet_continuousOn (r : ℝ) (hr : 0 < r)
    {s : Set ℝ} (hs : IsOpen s) {F : ℝ → IntervalFunctions r}
    (hF : ContDiffOn ℝ ∞ F s) (n : ℕ) :
    ContinuousOn (intervalFamilyJet r hr F n) (univ ×ˢ s) :=
  intervalExtension_family_continuousOn r hr
    (iteratedDeriv_contDiffOn_of_isOpen hs hF n).continuousOn

theorem intervalFamilyJet_hasDerivAt_y (r : ℝ) (hr : 0 < r)
    {s : Set ℝ} (hs : IsOpen s) {F : ℝ → IntervalFunctions r}
    (hF : ContDiffOn ℝ ∞ F s) (n : ℕ) (x : ℝ)
    {y : ℝ} (hy : y ∈ s) :
    HasDerivAt (fun t => intervalFamilyJet r hr F n (x, t))
      (intervalFamilyJet r hr F (n + 1) (x, y)) y := by
  have hd : HasDerivAt (iteratedDeriv n F) (iteratedDeriv (n + 1) F y) y := by
    rw [iteratedDeriv_succ]
    exact (((iteratedDeriv_contDiffOn_of_isOpen hs hF n).contDiffAt
      (hs.mem_nhds hy)).differentiableAt (by simp)).hasDerivAt
  exact intervalExtension_family_hasDerivAt r hr hd x

theorem intervalFamilyJet_hasDerivAt_x_of_primitive
    (r : ℝ) (hr : 0 < r) {s : Set ℝ} (hs : IsOpen s)
    {F P : ℝ → IntervalFunctions r} (hP : ContDiffOn ℝ ∞ P s)
    (c : ℝ)
    (hFP : ∀ y ∈ s,
      F y = ContinuousMap.const (Icc (-r) r) c + primitiveCLM r hr (P y))
    (n : ℕ) {x y : ℝ} (hx : x ∈ Ioo (-r) r) (hy : y ∈ s) :
    HasDerivAt (fun t => intervalFamilyJet r hr F n (t, y))
      (intervalFamilyJet r hr P n (x, y)) x := by
  cases n with
  | zero =>
      simp only [intervalFamilyJet, iteratedDeriv_zero]
      rw [hFP y hy]
      exact (intervalExtension_primitive_hasDerivAt r hr (P y) hx).const_add c
  | succ n =>
      have he : iteratedDeriv (n + 1) F y =
          primitiveCLM r hr (iteratedDeriv (n + 1) P y) := by
        have hev : F =ᶠ[𝓝 y] (fun t =>
            ContinuousMap.const (Icc (-r) r) c + primitiveCLM r hr (P t)) := by
          filter_upwards [hs.mem_nhds hy] with t ht
          exact hFP t ht
        rw [hev.iteratedDeriv_eq (n + 1), iteratedDeriv_const_add (Nat.zero_lt_succ n)]
        exact iteratedDeriv_clm_comp (primitiveCLM r hr) (n + 1)
          (hP.contDiffAt (hs.mem_nhds hy))
      simp only [intervalFamilyJet]
      rw [he]
      exact intervalExtension_primitive_hasDerivAt r hr _ hx

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

theorem matrix_column_basis_expansion (R : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    R *ᵥ Pi.single i (1 : ℝ) =
      R 0 i • Pi.single 0 (1 : ℝ) + R 1 i • Pi.single 1 (1 : ℝ) := by
  rw [Matrix.mulVec_single_one]
  funext k
  fin_cases k <;> simp

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem metric_compatibility (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k i j : Fin 2) :
    coordPartial k (fun q => g q i j) p =
      (∑ r, christoffel g r k i p * g p r j) +
        (∑ r, christoffel g r k j p * g p i r) := by
  have hlower (a b c : Fin 2) :
      (∑ r, christoffel g r a b p * g p c r) = christoffelFirstKind g a b p c := by
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using
      congrFun (metric_mul_christoffel hg hp a b) c
  have hsym : (∑ r, christoffel g r k i p * g p r j) =
      ∑ r, christoffel g r k i p * g p j r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [metric_coeff_symm hg hp r j]
  rw [hsym, hlower k i j, hlower k j i]
  simp only [christoffelFirstKind]
  rw [metric_coeff_partial_symm hg hU hp k j i]
  ring

namespace CompatibilityCalculus

end CompatibilityCalculus

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open scoped Matrix.Norms.Elementwise
open Filter

namespace SmoothLocal.Geometry

theorem coordPartial_eq_of_eventuallyEq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f h : Coord → V} {p : Coord} (heq : f =ᶠ[𝓝 p] h) (i : Fin 2) :
    coordPartial i f p = coordPartial i h p := by
  unfold coordPartial
  rw [heq.fderiv_eq]

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

namespace DarbouxJetCalculus

theorem coordPartial_eval (i j : Fin 2) (u : Coord) :
    coordPartial i (fun v : Coord => v j) u = if j = i then 1 else 0 := by
  simp [coordPartial, (hasFDerivAt_apply j u).fderiv, Pi.single_apply]

end DarbouxJetCalculus

theorem jetEnergy_at_height {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) (z : Coord → ℝ) :
    jetEnergy g p (fun i => coordPartial i z p) = heightEnergy g z p := by
  symm
  exact heightEnergy_polynomial z hg hp

theorem jetMixed_at_height (g : MetricField) (p : Coord) (z : Coord → ℝ) :
    jetMixed g p (coordPartial 0 (coordPartial 1 z) p) (fun i => coordPartial i z p) =
      covHessian g z p 0 1 := rfl

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

theorem iteratedDeriv_eq_of_derivative_sequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} (hs : IsOpen s) (H : ℕ → ℝ → E)
    (hd : ∀ n y, y ∈ s → HasDerivAt (H n) (H (n + 1) y) y) :
    ∀ n y, y ∈ s → iteratedDeriv n (H 0) y = H n y := by
  intro n
  induction n with
  | zero => intro y hy; simp only [iteratedDeriv_zero]
  | succ n hn =>
      intro y hy
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv n (H 0) =ᶠ[𝓝 y] H n := by
        filter_upwards [hs.mem_nhds hy] with t ht
        exact hn t ht
      exact ((hd n y hy).congr_of_eventuallyEq hev).deriv

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord} {p : Coord}

theorem metric_second_compatibility (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (d k i j : Fin 2) :
    coordPartial d (coordPartial k (fun q => g q i j)) p =
      (∑ r, (coordPartial d (christoffel g r k i) p * g p r j +
        christoffel g r k i p * coordPartial d (fun q => g q r j) p)) +
      (∑ r, (coordPartial d (christoffel g r k j) p * g p i r +
        christoffel g r k j p * coordPartial d (fun q => g q i r) p)) := by
  have heq : coordPartial k (fun q => g q i j) =ᶠ[𝓝 p]
      (fun q => (∑ r, christoffel g r k i q * g q r j) +
        (∑ r, christoffel g r k j q * g q i r)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact metric_compatibility hg hU hq k i j
  have hdg (a b : Fin 2) : DifferentiableAt ℝ (fun q => g q a b) p :=
    (((hg.1 a b) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdΓ (a b c : Fin 2) : DifferentiableAt ℝ (christoffel g a b c) p :=
    (((christoffel_contDiffOn hg hU a b c) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hA (r : Fin 2) : DifferentiableAt ℝ
      (fun q => christoffel g r k i q * g q r j) p := (hdΓ r k i).mul (hdg r j)
  have hB (r : Fin 2) : DifferentiableAt ℝ
      (fun q => christoffel g r k j q * g q i r) p := (hdΓ r k j).mul (hdg i r)
  change fderiv ℝ (coordPartial k (fun q => g q i j)) p (Pi.single d 1) = _
  rw [heq.fderiv_eq]
  change coordPartial d (fun q => (∑ r, christoffel g r k i q * g q r j) +
    (∑ r, christoffel g r k j q * g q i r)) p = _
  rw [HessianCalculus.coordPartial_add_at
      (DifferentiableAt.fun_sum fun r _ => hA r)
      (DifferentiableAt.fun_sum fun r _ => hB r) d,
    HessianCalculus.coordPartial_sum_two _ hA d,
    HessianCalculus.coordPartial_sum_two _ hB d]
  congr 1
  · apply Finset.sum_congr rfl
    intro r _
    exact HessianCalculus.coordPartial_mul_at (hdΓ r k i) (hdg r j) d
  · apply Finset.sum_congr rfl
    intro r _
    exact HessianCalculus.coordPartial_mul_at (hdΓ r k j) (hdg i r) d

def loweredRiemann (g : MetricField) (l k i j : Fin 2) (p : Coord) : ℝ :=
  ∑ r, g p l r * riemann g r k i j p

theorem loweredRiemann_skew_last (g : MetricField) (l k i j : Fin 2) (p : Coord) :
    loweredRiemann g l k i j p = -loweredRiemann g l k j i p := by
  simp only [loweredRiemann, riemann, Fin.sum_univ_two]
  ring

theorem loweredRiemann_skew_first_add (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (l k i j : Fin 2) :
    loweredRiemann g l k i j p + loweredRiemann g k l i j p = 0 := by
  have hc := coordPartial_comm (hg.1 k l) hU hp i j
  rw [metric_second_compatibility hg hU hp i j k l,
    metric_second_compatibility hg hU hp j i k l] at hc
  simp only [metric_compatibility hg hU hp, Fin.sum_univ_two] at hc
  simp only [loweredRiemann, riemann, Fin.sum_univ_two]
  simp only [metric_coeff_symm hg hp] at hc ⊢
  linear_combination hc

theorem loweredRiemann_skew_first (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (l k i j : Fin 2) :
    loweredRiemann g l k i j p = -loweredRiemann g k l i j p := by
  have h := loweredRiemann_skew_first_add hg hU hp l k i j
  linarith

theorem loweredRiemann_self_first (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (l i j : Fin 2) : loweredRiemann g l l i j p = 0 := by
  have h := loweredRiemann_skew_first_add hg hU hp l l i j
  linarith

theorem loweredRiemann_self_last (g : MetricField) (l k i : Fin 2) (p : Coord) :
    loweredRiemann g l k i i p = 0 := by
  have h := loweredRiemann_skew_last g l k i i p
  linarith

theorem loweredRiemann_0101 (hg : SmoothPositiveOn g U) (hp : p ∈ U) :
    loweredRiemann g 0 1 0 1 p = gaussianCurvature g p * (g p).det := by
  unfold loweredRiemann gaussianCurvature
  rw [div_mul_cancel₀ _ (metricDet_ne_zero hg hp)]

theorem loweredRiemann_factorization (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (l k i j : Fin 2) :
    loweredRiemann g l k i j p = gaussianCurvature g p *
      (g p l i * g p j k - g p l j * g p i k) := by
  have h10 (a b : Fin 2) : loweredRiemann g 1 0 a b p = -loweredRiemann g 0 1 a b p :=
    loweredRiemann_skew_first hg hU hp 1 0 a b
  have hrev : loweredRiemann g 0 1 1 0 p = -loweredRiemann g 0 1 0 1 p :=
    loweredRiemann_skew_last g 0 1 1 0 p
  have hsym : g p 1 0 = g p 0 1 := metric_coeff_symm hg hp 1 0
  fin_cases l <;> fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp only [Fin.mk_zero, Fin.mk_one, loweredRiemann_self_first hg hU hp, loweredRiemann_self_last,
      h10, hrev, loweredRiemann_0101 hg hp, Matrix.det_fin_two, hsym] <;> ring

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
namespace LowQuotient

variable {U : Set Coord} {a b : Coord → ℝ} {p : Coord}

theorem iterated_contDiffOn (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U)
    (ds : List (Fin 2)) : ContDiffOn ℝ ∞ (iteratedCoordPartial ds a) U := by
  induction ds with
  | nil => exact ha
  | cons i ds ih => exact partial_contDiffOn ih hU i

theorem iterated_differentiableAt (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U)
    (hp : p ∈ U) (ds : List (Fin 2)) :
    DifferentiableAt ℝ (iteratedCoordPartial ds a) p :=
  ((iterated_contDiffOn ha hU ds).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)

end LowQuotient
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

theorem contDiffOn_succ_of_continuous_partials
    {s : Set (ℝ × ℝ)} (hs : IsOpen s) {f fx fy : (ℝ × ℝ) → ℝ} (n : ℕ)
    (hfx : ContDiffOn ℝ n fx s) (hfy : ContDiffOn ℝ n fy s)
    (hdx : ∀ p ∈ s, HasDerivAt (fun x => f (x, p.2)) (fx p) p.1)
    (hdy : ∀ p ∈ s, HasDerivAt (fun y => f (p.1, y)) (fy p) p.2) :
    ContDiffOn ℝ (n + 1 : ℕ) f s := by
  have hd (p : ℝ × ℝ) (hp : p ∈ s) :
      HasFDerivAt f (jointDifferential (fx p) (fy p)) p :=
    hasFDerivAt_of_continuous_partials hs hfx.continuousOn hfy.continuousOn hdx hdy hp
  have hnext : ContDiffOn ℝ ((n : ℕ∞ω) + 1) f s := by
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
    refine ⟨fun p hp => (hd p hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hfield : ContDiffOn ℝ n (fun p => jointDifferential (fx p) (fy p)) s :=
      (contDiffOn_const.smulRight hfx).add (contDiffOn_const.smulRight hfy)
    exact hfield.congr (fun p hp => (hd p hp).fderiv)
  simpa only [Nat.cast_add, Nat.cast_one] using hnext

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace AffineCalculus

theorem coordPartial_const_mul_at {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (c : ℝ) (i : Fin 2) :
    coordPartial i (fun q => c * f q) p = c * coordPartial i f p := by
  simp [coordPartial, fderiv_const_mul hf]

theorem coordPartial_mul_const_at {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (c : ℝ) (i : Fin 2) :
    coordPartial i (fun q => f q * c) p = coordPartial i f p * c := by
  simpa only [mul_comm] using coordPartial_const_mul_at hf c i

end AffineCalculus

theorem coordPartial_affine_comp {f : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hf : DifferentiableAt ℝ f (affineCoordinates b R q)) (i : Fin 2) :
    coordPartial i (f ∘ affineCoordinates b R) q =
      ∑ a, R a i * coordPartial a f (affineCoordinates b R q) := by
  change fderiv ℝ (f ∘ affineCoordinates b R) q (Pi.single i 1) = _
  rw [fderiv_affine_comp_apply b R q (Pi.single i 1) hf,
    matrix_column_basis_expansion R i]
  simp only [map_add, map_smul, smul_eq_mul, Fin.sum_univ_two, coordPartial]

theorem coordPartial_affinePullbackMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hq : affineCoordinates b R q ∈ U) (k i j : Fin 2) :
    coordPartial k (fun p => affinePullbackMetric g b R p i j) q =
      ∑ a, ∑ c, ∑ d, R a i * R c j * R d k *
        coordPartial d (fun p => g p a c) (affineCoordinates b R q) := by
  have hd (a c : Fin 2) : DifferentiableAt ℝ (fun p => g p a c)
      (affineCoordinates b R q) :=
    (((hg.1 a c) _ hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
  have hdc (a c : Fin 2) : DifferentiableAt ℝ
      (fun p => g (affineCoordinates b R p) a c) q :=
    (hd a c).comp q (affineCoordinates_hasFDerivAt b R q).differentiableAt
  have hs (c : Fin 2) : DifferentiableAt ℝ
      (fun p => ∑ a, R a i * g (affineCoordinates b R p) a c) q :=
    DifferentiableAt.fun_sum fun a _ => (hdc a c).const_mul (R a i)
  have hchain (a c : Fin 2) :
      coordPartial k (fun p => g (affineCoordinates b R p) a c) q =
        ∑ d, R d k * coordPartial d (fun p => g p a c) (affineCoordinates b R q) :=
    coordPartial_affine_comp b R q (hd a c) k
  simp only [affinePullbackMetric, Matrix.mul_apply, Matrix.transpose_apply]
  rw [HessianCalculus.coordPartial_sum_two _
    (fun c => (hs c).mul_const (R c j)) k]
  simp_rw [AffineCalculus.coordPartial_mul_const_at (hs _) _ k,
    HessianCalculus.coordPartial_sum_two _
      (fun a => (hdc a _).const_mul (R a i)) k,
    AffineCalculus.coordPartial_const_mul_at (hdc _ _) _ k,
    hchain]
  simp only [Fin.sum_univ_two]
  ring

theorem christoffelFirstKind_affinePullback {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hq : affineCoordinates b R q ∈ U) (i j l : Fin 2) :
    christoffelFirstKind (affinePullbackMetric g b R) i j q l =
      ∑ a, ∑ c, ∑ d, R a l * R c i * R d j *
        christoffelFirstKind g c d (affineCoordinates b R q) a := by
  simp only [christoffelFirstKind, coordPartial_affinePullbackMetric hg hU b R q hq,
    Fin.sum_univ_two]
  ring

theorem christoffel_affinePullback_push {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (a i j : Fin 2) :
    (∑ l, R a l * christoffel (affinePullbackMetric g b R) l i j q) =
      ∑ c, ∑ d, R c i * R d j * christoffel g a c d (affineCoordinates b R q) := by
  have hRinj : Function.Injective R.mulVec := Matrix.mulVec_injective_of_isUnit hR
  have hgR := affinePullbackMetric_smoothPositive hg b R hRinj
  have hRt : IsUnit Rᵀ := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hR
  have hlower (l c d : Fin 2) :
      christoffelFirstKind g c d (affineCoordinates b R q) l =
        ∑ r, g (affineCoordinates b R q) l r *
          christoffel g r c d (affineCoordinates b R q) :=
    (congrFun (metric_mul_christoffel hg hq c d) l).symm
  have heq :
      (Rᵀ * g (affineCoordinates b R q)) *ᵥ
        (R *ᵥ (fun l => christoffel (affinePullbackMetric g b R) l i j q)) =
      (Rᵀ * g (affineCoordinates b R q)) *ᵥ
        (fun r => ∑ c, ∑ d, R c i * R d j *
          christoffel g r c d (affineCoordinates b R q)) := by
    rw [Matrix.mulVec_mulVec]
    change affinePullbackMetric g b R q *ᵥ
      (fun l => christoffel (affinePullbackMetric g b R) l i j q) = _
    rw [metric_mul_christoffel hgR hq i j]
    ext l
    rw [christoffelFirstKind_affinePullback hg hU b R q hq]
    simp only [hlower, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      dotProduct, Fin.sum_univ_two]
    ring
  have hv := Matrix.mulVec_injective_of_isUnit
    (hRt.mul (hg.2 (affineCoordinates b R q) hq).isUnit) heq
  exact congrFun hv a

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def stateBaseDomain (U : Set Coord) : Set DarbouxState := statePoint ⁻¹' U

def stateConnection (g : MetricField) (i j : Fin 2) (w : DarbouxState) : ℝ :=
  jetConnection g (statePoint w) i j (stateGradient w)

def stateMixed (g : MetricField) (w : DarbouxState) : ℝ :=
  jetMixed g (statePoint w) (w 4) (stateGradient w)

def stateDenominator (g : MetricField) (w : DarbouxState) : ℝ :=
  jetYY g (statePoint w) (w 5) (stateGradient w)

def stateNumerator (g : MetricField) (w : DarbouxState) : ℝ :=
  jetNumerator g (statePoint w) (w 4) (stateGradient w)

def darbouxStateDomain (g : MetricField) (U : Set Coord) : Set DarbouxState :=
  {w | statePoint w ∈ U ∧ stateDenominator g w ≠ 0}

theorem statePoint_contDiff : ContDiff ℝ ∞ statePoint := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ (0 : Fin 6)
  · exact contDiff_apply ℝ ℝ (1 : Fin 6)

theorem stateGradient_contDiff : ContDiff ℝ ∞ stateGradient := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ (2 : Fin 6)
  · exact contDiff_apply ℝ ℝ (3 : Fin 6)

theorem stateBaseDomain_isOpen {U : Set Coord} (hU : IsOpen U) :
    IsOpen (stateBaseDomain U) := hU.preimage statePoint_contDiff.continuous

variable {g : MetricField} {U : Set Coord}

theorem stateConnection_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (stateConnection g i j) (stateBaseDomain U) := by
  unfold stateConnection jetConnection
  apply ContDiffOn.sum
  intro r hr
  exact ((christoffel_contDiffOn hg hU r i j).comp statePoint_contDiff.contDiffOn
    (fun w hw => hw)).mul (((contDiff_apply ℝ ℝ r).comp stateGradient_contDiff).contDiffOn)

theorem stateMixed_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateMixed g) (stateBaseDomain U) :=
  (contDiffOn_apply ℝ ℝ 4 _).sub (stateConnection_contDiffOn hg hU 0 1)

theorem stateDenominator_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateDenominator g) (stateBaseDomain U) :=
  (contDiffOn_apply ℝ ℝ 5 _).sub (stateConnection_contDiffOn hg hU 1 1)

theorem stateEnergy_contDiffOn (hg : SmoothPositiveOn g U) :
    ContDiffOn ℝ ∞ (stateEnergy g) (stateBaseDomain U) := by
  have hcoef (i j : Fin 2) : ContDiffOn ℝ ∞ (fun w => g (statePoint w) i j) (stateBaseDomain U) :=
    (hg.1 i j).comp statePoint_contDiff.contDiffOn (fun w hw => hw)
  have hdet : ContDiffOn ℝ ∞ (fun w => (g (statePoint w)).det) (stateBaseDomain U) :=
    (metricDet_contDiffOn hg).comp statePoint_contDiff.contDiffOn (fun w hw => hw)
  have hv (i : Fin 2) : ContDiffOn ℝ ∞ (fun w => stateGradient w i) (stateBaseDomain U) :=
    ((contDiff_apply ℝ ℝ i).comp stateGradient_contDiff).contDiffOn
  exact hdet.sub ((((hcoef 1 1).mul ((hv 0).pow 2)).sub
    ((((hcoef 0 1).add (hcoef 1 0)).mul (hv 0)).mul (hv 1))).add
      ((hcoef 0 0).mul ((hv 1).pow 2)))

theorem stateNumerator_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateNumerator g) (stateBaseDomain U) :=
  ((stateMixed_contDiffOn hg hU).pow 2).add
    (((gaussianCurvature_contDiffOn hg hU).comp statePoint_contDiff.contDiffOn
      (fun _ hw => hw)).mul (stateEnergy_contDiffOn hg))

theorem darbouxStateDomain_isOpen (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    IsOpen (darbouxStateDomain g U) := by
  exact (stateDenominator_contDiffOn hg hU).continuousOn.isOpen_inter_preimage
    (stateBaseDomain_isOpen hU) isClosed_singleton.isOpen_compl

theorem sixVariableP_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (sixVariableP g) (darbouxStateDomain g U) := by
  have hsub : darbouxStateDomain g U ⊆ stateBaseDomain U := fun w hw => hw.1
  exact ((stateConnection_contDiffOn hg hU 0 0).mono hsub).add
    (((stateNumerator_contDiffOn hg hU).mono hsub).div
      ((stateDenominator_contDiffOn hg hU).mono hsub) (fun w hw => hw.2))

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace AffineCalculus

theorem coordPartial_sum_const_mul (f : Fin 2 → Coord → ℝ) (c : Fin 2 → ℝ)
    {p : Coord} (hf : ∀ a, DifferentiableAt ℝ (f a) p) (i : Fin 2) :
    coordPartial i (fun q => ∑ a, c a * f a q) p =
      ∑ a, c a * coordPartial i (f a) p := by
  rw [HessianCalculus.coordPartial_sum_two _ (fun a => (hf a).const_mul (c a)) i]
  apply Finset.sum_congr rfl
  intro a _
  exact coordPartial_const_mul_at (hf a) (c a) i

theorem coordPartial_double_sum_const_mul
    (f : Fin 2 → Fin 2 → Coord → ℝ) (c : Fin 2 → Fin 2 → ℝ)
    {p : Coord} (hf : ∀ a b, DifferentiableAt ℝ (f a b) p) (i : Fin 2) :
    coordPartial i (fun q => ∑ a, ∑ b, c a b * f a b q) p =
      ∑ a, ∑ b, c a b * coordPartial i (f a b) p := by
  rw [HessianCalculus.coordPartial_sum_two _
    (fun a => DifferentiableAt.fun_sum fun b _ => (hf a b).const_mul (c a b)) i]
  apply Finset.sum_congr rfl
  intro a _
  exact coordPartial_sum_const_mul (f a) (c a) (hf a) i

theorem pushed_connection_product
    (R : Matrix (Fin 2) (Fin 2) ℝ)
    (C D : Fin 2 → Fin 2 → Fin 2 → ℝ)
    (h : ∀ a i j, (∑ l, R a l * C l i j) = ∑ c, ∑ d, R c i * R d j * D a c d)
    (a i j k : Fin 2) :
    (∑ l, R a l * ∑ m, C m j k * C l i m) =
      ∑ c, ∑ d, ∑ e, ∑ f, R c i * R e j * R f k * D d e f * D a c d := by
  calc
    _ = ∑ m, C m j k * (∑ l, R a l * C l i m) := by
      simp only [Fin.sum_univ_two]
      ring
    _ = ∑ m, C m j k * (∑ c, ∑ d, R c i * R d m * D a c d) := by
      simp only [h]
    _ = ∑ c, ∑ d, R c i * D a c d * (∑ m, R d m * C m j k) := by
      simp only [Fin.sum_univ_two]
      ring
    _ = ∑ c, ∑ d, R c i * D a c d *
        (∑ e, ∑ f, R e j * R f k * D d e f) := by simp only [h]
    _ = _ := by simp only [Fin.sum_univ_two]; ring

end AffineCalculus

theorem coordPartial_christoffel_affinePullback_push
    {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (a i j k : Fin 2) :
    (∑ l, R a l * coordPartial i (christoffel (affinePullbackMetric g b R) l j k) q) =
      ∑ c, ∑ d, ∑ e, R c j * R d k * R e i *
        coordPartial e (christoffel g a c d) (affineCoordinates b R q) := by
  have hV := isOpen_affine_preimage hU b R
  have hgR := affinePullbackMetric_smoothPositive hg b R
    (Matrix.mulVec_injective_of_isUnit hR)
  have hL (l : Fin 2) : DifferentiableAt ℝ
      (christoffel (affinePullbackMetric g b R) l j k) q :=
    (((christoffel_contDiffOn hgR hV l j k) q hq).contDiffAt
      (hV.mem_nhds hq)).differentiableAt (by simp)
  have hG (c d : Fin 2) : DifferentiableAt ℝ (christoffel g a c d)
      (affineCoordinates b R q) :=
    (((christoffel_contDiffOn hg hU a c d) _ hq).contDiffAt
      (hU.mem_nhds hq)).differentiableAt (by simp)
  have hGc (c d : Fin 2) : DifferentiableAt ℝ
      (fun p => christoffel g a c d (affineCoordinates b R p)) q :=
    (hG c d).comp q (affineCoordinates_hasFDerivAt b R q).differentiableAt
  have hchain (c d : Fin 2) :
      coordPartial i (fun p => christoffel g a c d (affineCoordinates b R p)) q =
        ∑ e, R e i * coordPartial e (christoffel g a c d) (affineCoordinates b R q) :=
    coordPartial_affine_comp b R q (hG c d) i
  have heq : (fun p => ∑ l, R a l *
      christoffel (affinePullbackMetric g b R) l j k p) =ᶠ[𝓝 q]
      (fun p => ∑ c, ∑ d, R c j * R d k *
        christoffel g a c d (affineCoordinates b R p)) := by
    filter_upwards [hV.mem_nhds hq] with p hp
    exact christoffel_affinePullback_push hg hU b R hR p hp a j k
  calc
    _ = coordPartial i (fun p => ∑ l, R a l *
        christoffel (affinePullbackMetric g b R) l j k p) q :=
      (AffineCalculus.coordPartial_sum_const_mul _ _ hL i).symm
    _ = coordPartial i (fun p => ∑ c, ∑ d, R c j * R d k *
        christoffel g a c d (affineCoordinates b R p)) q := by
      unfold coordPartial
      rw [heq.fderiv_eq]
    _ = ∑ c, ∑ d, (R c j * R d k) * coordPartial i
        (fun p => christoffel g a c d (affineCoordinates b R p)) q :=
      AffineCalculus.coordPartial_double_sum_const_mul _ _ hGc i
    _ = _ := by
      simp_rw [hchain]
      simp only [Fin.sum_univ_two]
      ring

theorem riemann_affinePullback_push {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (a k i j : Fin 2) :
    (∑ l, R a l * riemann (affinePullbackMetric g b R) l k i j q) =
      ∑ c, ∑ d, ∑ e, R c k * R d i * R e j *
        riemann g a c d e (affineCoordinates b R q) := by
  let C := fun a i j => christoffel (affinePullbackMetric g b R) a i j q
  let D := fun a i j => christoffel g a i j (affineCoordinates b R q)
  have hp (a i j : Fin 2) : (∑ l, R a l * C l i j) =
      ∑ c, ∑ d, R c i * R d j * D a c d :=
    christoffel_affinePullback_push hg hU b R hR q hq a i j
  calc
    _ = (∑ l, R a l * coordPartial i
          (christoffel (affinePullbackMetric g b R) l j k) q) -
        (∑ l, R a l * coordPartial j
          (christoffel (affinePullbackMetric g b R) l i k) q) +
        (∑ l, R a l * ∑ m, C m j k * C l i m) -
        (∑ l, R a l * ∑ m, C m i k * C l j m) := by
      simp only [riemann, C, Fin.sum_univ_two]
      ring
    _ = (∑ c, ∑ d, ∑ e, R c j * R d k * R e i *
          coordPartial e (christoffel g a c d) (affineCoordinates b R q)) -
        (∑ c, ∑ d, ∑ e, R c i * R d k * R e j *
          coordPartial e (christoffel g a c d) (affineCoordinates b R q)) +
        (∑ c, ∑ d, ∑ e, ∑ f, R c i * R e j * R f k * D d e f * D a c d) -
        (∑ c, ∑ d, ∑ e, ∑ f, R c j * R e i * R f k * D d e f * D a c d) := by
      rw [coordPartial_christoffel_affinePullback_push hg hU b R hR q hq a i j k,
        coordPartial_christoffel_affinePullback_push hg hU b R hR q hq a j i k,
        AffineCalculus.pushed_connection_product R C D hp a i j k,
        AffineCalculus.pushed_connection_product R C D hp a j i k]
    _ = _ := by
      simp only [riemann, D, Fin.sum_univ_two]
      ring

theorem loweredRiemann_affinePullback {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (l k i j : Fin 2) :
    loweredRiemann (affinePullbackMetric g b R) l k i j q =
      ∑ a, ∑ c, ∑ d, ∑ e, R a l * R c k * R d i * R e j *
        loweredRiemann g a c d e (affineCoordinates b R q) := by
  calc
    _ = ∑ a, ∑ c, R a l * g (affineCoordinates b R q) a c *
        (∑ r, R c r * riemann (affinePullbackMetric g b R) r k i j q) := by
      simp only [loweredRiemann, affinePullbackMetric, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_two]
      ring
    _ = ∑ a, ∑ c, R a l * g (affineCoordinates b R q) a c *
        (∑ d, ∑ e, ∑ f, R d k * R e i * R f j *
          riemann g c d e f (affineCoordinates b R q)) := by
      simp_rw [riemann_affinePullback_push hg hU b R hR q hq]
    _ = _ := by simp only [loweredRiemann, Fin.sum_univ_two]; ring

theorem gaussianCurvature_affinePullback {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) :
    gaussianCurvature (affinePullbackMetric g b R) q =
      gaussianCurvature g (affineCoordinates b R q) := by
  have hgR := affinePullbackMetric_smoothPositive hg b R
    (Matrix.mulVec_injective_of_isUnit hR)
  have hsym : g (affineCoordinates b R q) 1 0 = g (affineCoordinates b R q) 0 1 :=
    metric_coeff_symm hg hq 1 0
  have hlow : loweredRiemann (affinePullbackMetric g b R) 0 1 0 1 q =
      gaussianCurvature g (affineCoordinates b R q) * (affinePullbackMetric g b R q).det := by
    rw [loweredRiemann_affinePullback hg hU b R hR q hq]
    simp only [loweredRiemann_factorization hg hU hq,
      affinePullbackMetric, Matrix.det_fin_two, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two, hsym]
    ring
  change loweredRiemann (affinePullbackMetric g b R) 0 1 0 1 q /
    (affinePullbackMetric g b R q).det = _
  rw [hlow, mul_div_cancel_right₀ _ (metricDet_ne_zero hgR hq)]

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

namespace CoordinateBound

theorem iterated_sub {f h : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (ds : List (Fin 2)) {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds (fun x => f x - h x) p =
      iteratedCoordPartial ds f p - iteratedCoordPartial ds h p := by
  induction ds generalizing p with
  | nil => rfl
  | cons i ds ih =>
    have he : iteratedCoordPartial ds (fun x => f x - h x) =ᶠ[𝓝 p]
        (fun x => iteratedCoordPartial ds f x - iteratedCoordPartial ds h x) := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact ih hx
    change coordPartial i (iteratedCoordPartial ds (fun x => f x - h x)) p = _
    rw [coordPartial_eq_of_eventuallyEq he i]
    exact HessianCalculus.coordPartial_sub_at
      (LowQuotient.iterated_differentiableAt hf hU hp ds)
      (LowQuotient.iterated_differentiableAt hh hU hp ds) i

end CoordinateBound
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry SmoothLocal.ODE

theorem coordinateRectangle_isOpen (R a b : ℝ) : IsOpen (coordinateRectangle R a b) := by
  change IsOpen (((fun p : Coord => p 0) ⁻¹' Ioo (-R) R) ∩
    ((fun p : Coord => p 1) ⁻¹' Ioo a b))
  exact (isOpen_Ioo.preimage (continuous_apply 0)).inter
    (isOpen_Ioo.preimage (continuous_apply 1))

theorem point_mem_rectangle {R a b x y : ℝ}
    (hx : x ∈ Ioo (-R) R) (hy : y ∈ Ioo a b) :
    coordinatePoint x y ∈ coordinateRectangle R a b := by
  simpa [coordinateRectangle, coordinatePoint] using And.intro hx hy

theorem point_eta (p : Coord) : coordinatePoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> simp [coordinatePoint]

theorem point_hasDerivAt_t (x y : ℝ) :
    HasDerivAt (fun t => coordinatePoint t y) (Pi.single 0 (1 : ℝ) : Coord) x := by
  simpa [coordinatePoint] using
    ((hasDerivAt_id x).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add_const
      (y • (Pi.single 1 (1 : ℝ) : Coord))

variable {B : Coord → ℝ} {R a b : ℝ}

theorem parameterDerivative_smooth_on_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) :
    ∀ n, ContDiffOn ℝ ∞ (curvatureYDerivative B n) (coordinateRectangle R a b) := by
  intro n
  induction n with
  | zero => exact hB
  | succ n hn => exact partial_contDiffOn hn (coordinateRectangle_isOpen R a b) 1

theorem compact_t_mem_rectangle_interval {r : ℝ} (hrR : r < R) (x : Icc (-r) r) :
    (x : ℝ) ∈ Ioo (-R) R :=
  ⟨(neg_lt_neg hrR).trans_le x.2.1, x.2.2.trans_lt hrR⟩

theorem coefficientFamily_apply_on_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hrR : r < R) {y : ℝ} (hy : y ∈ Ioo a b) (x : Icc (-r) r) :
    coordinateCurvatureFamily B r y x = B (coordinatePoint x y) := by
  have hc : Continuous (fun t : Icc (-r) r => B (coordinatePoint t y)) :=
    hB.continuousOn.comp_continuous (by unfold coordinatePoint; fun_prop)
      (fun t => point_mem_rectangle (compact_t_mem_rectangle_interval hrR t) hy)
  unfold coordinateCurvatureFamily
  rw [ContinuousMap.mkD_of_continuous hc]
  rfl

theorem coefficientFamily_contDiffOn_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hrR : r < R) :
    ContDiffOn ℝ ∞ (coordinateCurvatureFamily B r) (Ioo a b) := by
  let H : ℕ → ℝ → Icc (-r) r → ℝ :=
    fun n y x => curvatureYDerivative B n (coordinatePoint x y)
  have hmem (y : ℝ) (hy : y ∈ Ioo a b) (x : Icc (-r) r) :
      coordinatePoint x y ∈ coordinateRectangle R a b :=
    point_mem_rectangle (compact_t_mem_rectangle_interval hrR x) hy
  have hjoint (n : ℕ) : ContinuousOn (Function.uncurry (H n))
      (Ioo a b ×ˢ (Set.univ : Set (Icc (-r) r))) := by
    have hmap : Continuous (fun p : ℝ × Icc (-r) r => coordinatePoint p.2 p.1) := by
      unfold coordinatePoint
      fun_prop
    exact (parameterDerivative_smooth_on_rectangle hB n).continuousOn.comp
      hmap.continuousOn (fun p hp => hmem p.1 hp.1 p.2)
  have hderiv (n : ℕ) (y : ℝ) (hy : y ∈ Ioo a b) (x : Icc (-r) r) :
      HasDerivAt (fun t => H n t x) (H (n + 1) y x) y := by
    have hd : DifferentiableAt ℝ (curvatureYDerivative B n) (coordinatePoint x y) :=
      ((parameterDerivative_smooth_on_rectangle hB n).contDiffAt
        ((coordinateRectangle_isOpen R a b).mem_nhds (hmem y hy x))).differentiableAt
          (by simp)
    exact hd.hasFDerivAt.comp_hasDerivAt y (coordinatePoint_hasDerivAt_y x y)
  exact smooth_curry_of_joint_derivative_sequence H hjoint hderiv 0

theorem coefficientFamily_jet_apply_on_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hrR : r < R) (n : ℕ) (x : Icc (-r) r)
    {y : ℝ} (hy : y ∈ Ioo a b) :
    iteratedDeriv n (coordinateCurvatureFamily B r) y x =
      curvatureYDerivative B n (coordinatePoint x y) := by
  have heval := iteratedDeriv_clm_comp (ContinuousMap.evalCLM ℝ x) n
    ((coefficientFamily_contDiffOn_rectangle hB r hrR).contDiffAt
      (isOpen_Ioo.mem_nhds hy))
  have hev : (fun t => coordinateCurvatureFamily B r t x) =ᶠ[𝓝 y]
      (fun t => B (coordinatePoint x t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    exact coefficientFamily_apply_on_rectangle hB r hrR ht x
  have hdseq (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun v => curvatureYDerivative B j (coordinatePoint x v))
        (curvatureYDerivative B (j + 1) (coordinatePoint x t)) t := by
    have hmem : coordinatePoint x t ∈ coordinateRectangle R a b :=
      point_mem_rectangle (compact_t_mem_rectangle_interval hrR x) ht
    have hd : DifferentiableAt ℝ (curvatureYDerivative B j) (coordinatePoint x t) :=
      ((parameterDerivative_smooth_on_rectangle hB j).contDiffAt
        ((coordinateRectangle_isOpen R a b).mem_nhds hmem)).differentiableAt (by simp)
    exact hd.hasFDerivAt.comp_hasDerivAt t (coordinatePoint_hasDerivAt_y x t)
  have hseq := iteratedDeriv_eq_of_derivative_sequence isOpen_Ioo
    (fun j t => curvatureYDerivative B j (coordinatePoint x t)) hdseq n y hy
  calc
    iteratedDeriv n (coordinateCurvatureFamily B r) y x =
        iteratedDeriv n (fun t => coordinateCurvatureFamily B r t x) y := heval.symm
    _ = iteratedDeriv n (fun t => B (coordinatePoint x t)) y := hev.iteratedDeriv_eq n
    _ = curvatureYDerivative B n (coordinatePoint x y) := hseq

theorem coefficientFamily_jet_contDiffOn_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hr : 0 < r) (hrR : r < R) (n : ℕ) :
    ContDiffOn ℝ ∞ (intervalFamilyJet r hr (coordinateCurvatureFamily B r) n)
      (Ioo (-r) r ×ˢ Ioo a b) := by
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => coordinatePoint p.1 p.2) := by
    unfold coordinatePoint
    fun_prop
  have hmem : MapsTo (fun p : ℝ × ℝ => coordinatePoint p.1 p.2)
      (Ioo (-r) r ×ˢ Ioo a b) (coordinateRectangle R a b) := by
    intro p hp
    exact point_mem_rectangle
      ⟨(neg_lt_neg hrR).trans hp.1.1, hp.1.2.trans hrR⟩ hp.2
  have hc := (parameterDerivative_smooth_on_rectangle hB n).comp hmap.contDiffOn hmem
  apply hc.congr
  intro p hp
  unfold intervalFamilyJet
  rw [intervalExtension_apply_of_mem r hr _ ⟨hp.1.1.le, hp.1.2.le⟩]
  exact coefficientFamily_jet_apply_on_rectangle hB r hrR n _ hp.2

theorem primitiveFamily_joint_smooth
    (r : ℝ) (hr : 0 < r) {F : ℝ → IntervalFunctions r}
    (hF : ContDiffOn ℝ ∞ F (Ioo a b))
    (hFjets : ∀ j, ContDiffOn ℝ ∞ (intervalFamilyJet r hr F j)
      (Ioo (-r) r ×ˢ Ioo a b)) :
    ∀ j, ContDiffOn ℝ ∞
      (intervalFamilyJet r hr (fun y => primitiveCLM r hr (F y)) j)
      (Ioo (-r) r ×ˢ Ioo a b) := by
  let P : ℝ → IntervalFunctions r := fun y => primitiveCLM r hr (F y)
  let D : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo a b
  have hD : IsOpen D := isOpen_Ioo.prod isOpen_Ioo
  have hP : ContDiffOn ℝ ∞ P (Ioo a b) := contDiffOn_const.clm_apply hF
  have hdx (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun x => intervalFamilyJet r hr P j (x, p.2))
        (intervalFamilyJet r hr F j p) p.1 := by
    apply intervalFamilyJet_hasDerivAt_x_of_primitive r hr isOpen_Ioo hF 0 _ j hp.1 hp.2
    intro y hy
    change primitiveCLM r hr (F y) = 0 + primitiveCLM r hr (F y)
    rw [zero_add]
  have hdy (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun y => intervalFamilyJet r hr P j (p.1, y))
        (intervalFamilyJet r hr P (j + 1) p) p.2 :=
    intervalFamilyJet_hasDerivAt_y r hr isOpen_Ioo hP j p.1 hp.2
  have hnat : ∀ n : ℕ, ∀ j,
      ContDiffOn ℝ n (intervalFamilyJet r hr P j) D := by
    intro n
    induction n with
    | zero =>
        intro j
        simpa only [Nat.cast_zero, contDiffOn_zero] using
          (intervalFamilyJet_continuousOn r hr isOpen_Ioo hP j).mono
            (fun p hp => ⟨mem_univ p.1, hp.2⟩)
    | succ n hn =>
        intro j
        exact contDiffOn_succ_of_continuous_partials hD n
          (contDiffOn_infty.mp (hFjets j) n) (hn (j + 1)) (hdx j) (hdy j)
  intro j
  exact contDiffOn_infty.mpr (fun n => hnat n j)

def clampedPrimitive (B : Coord → ℝ) (r : ℝ) (hr : 0 < r) (p : ℝ × ℝ) : ℝ :=
  intervalExtension r hr (primitiveCLM r hr (coordinateCurvatureFamily B r p.2)) p.1

theorem clampedPrimitive_contDiffOn
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    ContDiffOn ℝ ∞ (clampedPrimitive B r hr) (Ioo (-r) r ×ˢ Ioo a b) := by
  have h := primitiveFamily_joint_smooth r hr
    (coefficientFamily_contDiffOn_rectangle hB r hrR)
    (coefficientFamily_jet_contDiffOn_rectangle hB r hr hrR) 0
  apply h.congr
  intro p hp
  simp only [intervalFamilyJet, iteratedDeriv_zero, clampedPrimitive]

theorem clampedPrimitive_eq_integral
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hr : 0 < r) (hrR : r < R)
    {x y : ℝ} (hx : x ∈ Ioo (-r) r) (hy : y ∈ Ioo a b) :
    clampedPrimitive B r hr (x, y) = ∫ t in 0..x, B (coordinatePoint t y) := by
  unfold clampedPrimitive
  rw [intervalExtension_apply_of_mem r hr _ ⟨hx.1.le, hx.2.le⟩, primitiveCLM_apply]
  apply intervalIntegral.integral_congr
  intro t ht
  have hz : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr.le⟩
  have htmem : t ∈ Icc (-r) r := uIcc_subset_Icc hz ⟨hx.1.le, hx.2.le⟩ ht
  rw [intervalExtension_apply_of_mem r hr _ htmem,
    coefficientFamily_apply_on_rectangle hB r hrR hy]

theorem coordinatePrimitive_contDiffOn_inner
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    ContDiffOn ℝ ∞ (coordinatePrimitive B) (coordinateRectangle r a b) := by
  have hmap : ContDiff ℝ ∞ (fun p : Coord => (p 0, p 1)) := by fun_prop
  have hmem : MapsTo (fun p : Coord => (p 0, p 1)) (coordinateRectangle r a b)
      (Ioo (-r) r ×ˢ Ioo a b) := fun _ hp => hp
  have hc := (clampedPrimitive_contDiffOn hB r hr hrR).comp hmap.contDiffOn hmem
  apply hc.congr
  intro p hp
  exact (clampedPrimitive_eq_integral hB r hr hrR hp.1 hp.2).symm

theorem coordinatePrimitive_contDiffOn
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) :
    ContDiffOn ℝ ∞ (coordinatePrimitive B) (coordinateRectangle R a b) := by
  intro p hp
  obtain ⟨r, hpr, hrR⟩ := exists_between (abs_lt.mpr hp.1)
  have hr : 0 < r := (abs_nonneg (p 0)).trans_lt hpr
  have hpmem : p ∈ coordinateRectangle r a b := ⟨abs_lt.mp hpr, hp.2⟩
  exact ((coordinatePrimitive_contDiffOn_inner hB r hr hrR).contDiffAt
    ((coordinateRectangle_isOpen r a b).mem_nhds hpmem)).contDiffWithinAt

theorem coordinatePrimitive_partial_t
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b) :
    coordPartial 0 (coordinatePrimitive B) p = B p := by
  have hslice : ContinuousOn (fun t => B (coordinatePoint t (p 1))) (Ioo (-R) R) :=
    hB.continuousOn.comp (by unfold coordinatePoint; fun_prop)
      (fun t ht => point_mem_rectangle ht hp.2)
  have hz : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
  have hseg : uIcc 0 (p 0) ⊆ Ioo (-R) R := by
    intro t ht
    exact ⟨lt_of_lt_of_le (lt_min hz.1 hp.1.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hz.2 hp.1.2)⟩
  have hftc := intervalIntegral.integral_hasDerivAt_right
    (hslice.mono hseg).intervalIntegrable
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hslice (p 0) hp.1)
    (hslice.continuousAt (isOpen_Ioo.mem_nhds hp.1))
  have hftc' : HasDerivAt (fun t => coordinatePrimitive B (coordinatePoint t (p 1)))
      (B p) (p 0) := by
    rw [point_eta] at hftc
    simpa [coordinatePrimitive, coordinatePoint] using hftc
  have hd : DifferentiableAt ℝ (coordinatePrimitive B) (coordinatePoint (p 0) (p 1)) := by
    rw [point_eta]
    exact ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by simp)
  have hchain := hd.hasFDerivAt.comp_hasDerivAt (p 0) (point_hasDerivAt_t (p 0) (p 1))
  have hcoord : HasDerivAt (fun t => coordinatePrimitive B (coordinatePoint t (p 1)))
      (coordPartial 0 (coordinatePrimitive B) p) (p 0) := by
    simpa only [point_eta, Function.comp_def, coordPartial] using hchain
  exact hcoord.unique hftc'

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted

def hyperbolicOperator (P S v : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 1 (coordPartial 1 v) p -
    P p * coordPartial 0 (coordPartial 1 v) p -
    S p * coordPartial 0 (coordPartial 0 v) p

def energyFlux (P S v : Coord → ℝ) (p : Coord) : ℝ :=
  P p * (coordPartial 1 v p) ^ 2 / 2 +
    S p * coordPartial 0 v p * coordPartial 1 v p

def energyCoefficientError (P S bTheta bXi v : Coord → ℝ) (p : Coord) : ℝ :=
  (bTheta p - coordPartial 0 P p / 2) * (coordPartial 1 v p) ^ 2 +
    (bXi p - coordPartial 0 S p) * coordPartial 0 v p * coordPartial 1 v p +
    coordPartial 1 S p / 2 * (coordPartial 0 v p) ^ 2

variable {P S bTheta bXi v R : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem energyDensity_partial_theta
    (hS : DifferentiableAt ℝ S p)
    (hvt : DifferentiableAt ℝ (coordPartial 1 v) p)
    (hvx : DifferentiableAt ℝ (coordPartial 0 v) p) :
    coordPartial 1 (energyDensity S v) p =
      coordPartial 1 v p * coordPartial 1 (coordPartial 1 v) p +
      S p * coordPartial 0 v p * coordPartial 1 (coordPartial 0 v) p +
      coordPartial 1 S p / 2 * (coordPartial 0 v p) ^ 2 := by
  have hd := ((hvt.hasFDerivAt.fun_mul hvt.hasFDerivAt).add
    (hS.hasFDerivAt.fun_mul (hvx.hasFDerivAt.fun_mul hvx.hasFDerivAt))).mul_const
      (1 / 2 : ℝ)
  simp only [Pi.add_def, coordPartial, one_div] at hd
  unfold energyDensity
  simp only [div_eq_mul_inv, pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem energyFlux_partial_xi
    (hP : DifferentiableAt ℝ P p) (hS : DifferentiableAt ℝ S p)
    (hvt : DifferentiableAt ℝ (coordPartial 1 v) p)
    (hvx : DifferentiableAt ℝ (coordPartial 0 v) p) :
    coordPartial 0 (energyFlux P S v) p =
      coordPartial 0 P p / 2 * (coordPartial 1 v p) ^ 2 +
      P p * coordPartial 1 v p * coordPartial 0 (coordPartial 1 v) p +
      coordPartial 0 S p * coordPartial 0 v p * coordPartial 1 v p +
      S p * coordPartial 0 (coordPartial 0 v) p * coordPartial 1 v p +
      S p * coordPartial 0 v p * coordPartial 0 (coordPartial 1 v) p := by
  have hd := ((hP.hasFDerivAt.fun_mul
    (hvt.hasFDerivAt.fun_mul hvt.hasFDerivAt)).mul_const (1 / 2 : ℝ)).add
      ((hS.hasFDerivAt.fun_mul hvx.hasFDerivAt).fun_mul hvt.hasFDerivAt)
  simp only [Pi.add_def, coordPartial, one_div] at hd
  unfold energyFlux
  simp only [div_eq_mul_inv, pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem energy_density_flux_identity
    (hP : DifferentiableAt ℝ P p) (hS : DifferentiableAt ℝ S p)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hp : p ∈ U)
    (hEq : hyperbolicOperator P S v p =
      bTheta p * coordPartial 1 v p + bXi p * coordPartial 0 v p + R p) :
    coordPartial 1 (energyDensity S v) p - coordPartial 0 (energyFlux P S v) p =
      energyCoefficientError P S bTheta bXi v p + R p * coordPartial 1 v p := by
  have hd (i : Fin 2) : DifferentiableAt ℝ (coordPartial i v) p :=
    ((partial_contDiffOn hv hU i).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  rw [energyDensity_partial_theta hS (hd 1) (hd 0),
    energyFlux_partial_xi hP hS (hd 1) (hd 0), coordPartial_comm hv hU hp 1 0]
  unfold hyperbolicOperator at hEq
  unfold energyCoefficientError
  nlinarith [congrArg (fun x : ℝ => x * coordPartial 1 v p) hEq]

theorem energy_fields_contDiffOn
    (hU : IsOpen U) (hP : ContDiffOn ℝ ∞ P U) (hS : ContDiffOn ℝ ∞ S U)
    (hbt : ContDiffOn ℝ ∞ bTheta U) (hbx : ContDiffOn ℝ ∞ bXi U)
    (hv : ContDiffOn ℝ ∞ v U) :
    ContDiffOn ℝ ∞ (energyDensity S v) U ∧
    ContDiffOn ℝ ∞ (energyFlux P S v) U ∧
    ContDiffOn ℝ ∞ (energyCoefficientError P S bTheta bXi v) U := by
  have ht := partial_contDiffOn hv hU 1
  have hx := partial_contDiffOn hv hU 0
  have hPx := partial_contDiffOn hP hU 0
  have hSx := partial_contDiffOn hS hU 0
  have hSt := partial_contDiffOn hS hU 1
  exact ⟨((ht.pow 2).add (hS.mul (hx.pow 2))).div_const 2,
    ((hP.mul (ht.pow 2)).div_const 2).add ((hS.mul hx).mul ht),
    (((hbt.sub (hPx.div_const 2)).mul (ht.pow 2)).add
      (((hbx.sub hSx).mul hx).mul ht)).add ((hSt.div_const 2).mul (hx.pow 2))⟩

theorem energyDensity_nonneg (hS : 0 ≤ S p) : 0 ≤ energyDensity S v p := by
  unfold energyDensity
  positivity

theorem scalar_flux_bound (P S a b : ℝ) (hS : 0 ≤ S) :
    |P * a ^ 2 / 2 + S * b * a| ≤
      (|P| + Real.sqrt S) * ((a ^ 2 + S * b ^ 2) / 2) := by
  have hs := Real.sqrt_nonneg S
  have hs2 := Real.sq_sqrt hS
  have hab : 2 * Real.sqrt S * (|a| * |b|) ≤ a ^ 2 + S * b ^ 2 := by
    nlinarith [sq_nonneg (|a| - Real.sqrt S * |b|), sq_abs a, sq_abs b]
  have hab' := mul_le_mul_of_nonneg_left hab hs
  have hsimpl : Real.sqrt S * (2 * Real.sqrt S * (|a| * |b|)) =
      2 * S * |b| * |a| := by
    calc
      _ = 2 * (Real.sqrt S) ^ 2 * |b| * |a| := by ring
      _ = _ := by rw [hs2]
  rw [hsimpl] at hab'
  have hsa : S * |b| * |a| ≤ Real.sqrt S * ((a ^ 2 + S * b ^ 2) / 2) := by
    nlinarith only [hab']
  calc
    _ ≤ |P * a ^ 2 / 2| + |S * b * a| := abs_add_le _ _
    _ = |P| * a ^ 2 / 2 + S * |b| * |a| := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg a),
        abs_mul, abs_mul, abs_of_nonneg hS]
      norm_num
    _ ≤ |P| * ((a ^ 2 + S * b ^ 2) / 2) +
        Real.sqrt S * ((a ^ 2 + S * b ^ 2) / 2) := by
      have hsb := mul_nonneg (abs_nonneg P) (mul_nonneg hS (sq_nonneg b))
      nlinarith
    _ = _ := by ring

theorem energyFlux_abs_le (hS : 0 ≤ S p) :
    |energyFlux P S v p| ≤ (|P p| + Real.sqrt (S p)) * energyDensity S v p :=
  scalar_flux_bound (P p) (S p) (coordPartial 1 v p) (coordPartial 0 v p) hS

theorem inward_boundary_nonpositive {left right : Coord} {c : ℝ}
    (hSl : 0 ≤ S left) (hSr : 0 ≤ S right)
    (hcl : |P left| + Real.sqrt (S left) ≤ c)
    (hcr : |P right| + Real.sqrt (S right) ≤ c) :
    energyFlux P S v right - energyFlux P S v left -
      c * (energyDensity S v right + energyDensity S v left) ≤ 0 := by
  have hl := (energyFlux_abs_le (P := P) (v := v) hSl).trans
    (mul_le_mul_of_nonneg_right hcl (energyDensity_nonneg (v := v) hSl))
  have hr := (energyFlux_abs_le (P := P) (v := v) hSr).trans
    (mul_le_mul_of_nonneg_right hcr (energyDensity_nonneg (v := v) hSr))
  have hll := (abs_le.mp hl).1
  have hrr := (abs_le.mp hr).2
  linarith

theorem scalar_coefficient_error_bound
    {s0 S M bt bx Px Sx St a b : ℝ} (hs0 : 0 < s0) (hS : s0 ≤ S)
    (hM : 0 ≤ M) (hbt : |bt| ≤ M) (hbx : |bx| ≤ M)
    (hPx : |Px| ≤ M) (hSx : |Sx| ≤ M) (hSt : |St| ≤ M) :
    |(bt - Px / 2) * a ^ 2 + (bx - Sx) * b * a + St / 2 * b ^ 2| ≤
      (8 * M * (1 + 1 / s0)) * ((a ^ 2 + S * b ^ 2) / 2) := by
  have hA : |bt - Px / 2| ≤ 2 * M := by
    have hh := abs_sub bt (Px / 2)
    rw [abs_div] at hh
    norm_num at hh
    linarith
  have hB : |bx - Sx| ≤ 2 * M := (abs_sub _ _).trans (by linarith)
  have hC : |St / 2| ≤ M := by rw [abs_div]; norm_num; linarith
  have hab : |b| * |a| ≤ (a ^ 2 + b ^ 2) / 2 := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have hrough :
      |(bt - Px / 2) * a ^ 2 + (bx - Sx) * b * a + St / 2 * b ^ 2| ≤
        4 * M * (a ^ 2 + b ^ 2) := by
    calc
      _ ≤ |(bt - Px / 2) * a ^ 2| + |(bx - Sx) * b * a| + |St / 2 * b ^ 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |bt - Px / 2| * a ^ 2 + |bx - Sx| * (|b| * |a|) + |St / 2| * b ^ 2 := by
        simp only [abs_mul, abs_of_nonneg (sq_nonneg a), abs_of_nonneg (sq_nonneg b)]
        ring
      _ ≤ (2 * M) * a ^ 2 + (2 * M) * ((a ^ 2 + b ^ 2) / 2) + M * b ^ 2 := by
        gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hM (sq_nonneg a), mul_nonneg hM (sq_nonneg b)]
  have hinv : 0 < 1 / s0 := one_div_pos.mpr hs0
  have hsb : b ^ 2 ≤ (1 / s0) * (S * b ^ 2) := by
    have hh := mul_le_mul_of_nonneg_right hS (sq_nonneg b)
    have hh' : b ^ 2 ≤ (S * b ^ 2) / s0 :=
      (le_div_iff₀ hs0).2 (by nlinarith)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh'
  have hcompare : a ^ 2 + b ^ 2 ≤ (1 + 1 / s0) * (a ^ 2 + S * b ^ 2) := by
    nlinarith [mul_nonneg hinv.le (sq_nonneg a), mul_nonneg (hs0.le.trans hS) (sq_nonneg b)]
  exact hrough.trans (by nlinarith [mul_le_mul_of_nonneg_left hcompare (by positivity : 0 ≤ 4 * M)])

theorem energyCoefficientError_abs_le
    {s0 M : ℝ} (hs0 : 0 < s0) (hS : s0 ≤ S p) (hM : 0 ≤ M)
    (hbt : |bTheta p| ≤ M) (hbx : |bXi p| ≤ M)
    (hPx : |coordPartial 0 P p| ≤ M) (hSx : |coordPartial 0 S p| ≤ M)
    (hSt : |coordPartial 1 S p| ≤ M) :
    |energyCoefficientError P S bTheta bXi v p| ≤
      (8 * M * (1 + 1 / s0)) * energyDensity S v p :=
  scalar_coefficient_error_bound hs0 hS hM hbt hbx hPx hSx hSt

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem statePoint_segment {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) (sigma : ℝ) :
    statePoint (stateSegment w0 w1 sigma) = statePoint w0 := by
  have h0 : w0 0 = w1 0 := congrFun hp 0
  have h1 : w0 1 = w1 1 := congrFun hp 1
  ext i
  fin_cases i <;> simp [statePoint, stateSegment, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ← h0, ← h1] <;> ring

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def swapCoordinateIndex (i : Fin 2) : Fin 2 := ![1, 0] i

def coordinateSwap : Coord → Coord := affineCoordinates 0 coordinateSwapMatrix

@[simp] theorem swapCoordinateIndex_zero : swapCoordinateIndex 0 = 1 := rfl
@[simp] theorem swapCoordinateIndex_one : swapCoordinateIndex 1 = 0 := rfl

@[simp] theorem swapCoordinateIndex_involutive (i : Fin 2) :
    swapCoordinateIndex (swapCoordinateIndex i) = i := by
  fin_cases i <;> rfl

@[simp] theorem coordinateSwap_apply (p : Coord) (i : Fin 2) :
    coordinateSwap p i = p (swapCoordinateIndex i) := by
  fin_cases i <;>
    simp [coordinateSwap, affineCoordinates, coordinateSwapMatrix,
      dotProduct, Fin.sum_univ_two, swapCoordinateIndex]

@[simp] theorem coordinateSwap_involutive (p : Coord) :
    coordinateSwap (coordinateSwap p) = p := by
  ext i
  simp

@[simp] theorem coordinateSwapMatrix_det : coordinateSwapMatrix.det = -1 := by
  norm_num [coordinateSwapMatrix, Matrix.det_fin_two]

theorem coordinateSwapMatrix_isUnit : IsUnit coordinateSwapMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det, coordinateSwapMatrix_det]
  exact isUnit_neg_one

theorem coordinateSwap_contDiff : ContDiff ℝ ∞ coordinateSwap :=
  affineCoordinates_contDiff 0 coordinateSwapMatrix

theorem coordinateSwap_preimage_isOpen {U : Set Coord} (hU : IsOpen U) :
    IsOpen (coordinateSwap ⁻¹' U) :=
  hU.preimage coordinateSwap_contDiff.continuous

theorem swappedMetric_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) :
    SmoothPositiveOn (swappedMetric g) (coordinateSwap ⁻¹' U) :=
  affinePullbackMetric_smoothPositive hg 0 coordinateSwapMatrix
    (Matrix.mulVec_injective_of_isUnit coordinateSwapMatrix_isUnit)

@[simp] theorem swappedMetric_apply (g : MetricField) (p : Coord) (i j : Fin 2) :
    swappedMetric g p i j =
      g (coordinateSwap p) (swapCoordinateIndex i) (swapCoordinateIndex j) := by
  fin_cases i <;> fin_cases j <;>
    simp [swappedMetric, affinePullbackMetric, coordinateSwapMatrix,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      coordinateSwap, swapCoordinateIndex]

@[simp] theorem swappedMetric_det (g : MetricField) (p : Coord) :
    (swappedMetric g p).det = (g (coordinateSwap p)).det := by
  simp only [Matrix.det_fin_two, swappedMetric_apply,
    swapCoordinateIndex_zero, swapCoordinateIndex_one]
  ring

theorem gaussianCurvature_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) :
    gaussianCurvature (swappedMetric g) p = gaussianCurvature g (coordinateSwap p) :=
  gaussianCurvature_affinePullback hg hU 0 coordinateSwapMatrix
    coordinateSwapMatrix_isUnit p hp

theorem christoffel_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (k i j : Fin 2) :
    christoffel (swappedMetric g) k i j p =
      christoffel g (swapCoordinateIndex k) (swapCoordinateIndex i)
        (swapCoordinateIndex j) (coordinateSwap p) := by
  have h := christoffel_affinePullback_push hg hU 0 coordinateSwapMatrix
    coordinateSwapMatrix_isUnit p hp (swapCoordinateIndex k) i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simpa [coordinateSwapMatrix, swapCoordinateIndex, Fin.sum_univ_two,
      swappedMetric, coordinateSwap] using h

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.ODE

def pairPrimitive (B : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ t in 0..p.1, B (t, p.2)

def pairPartialY (B : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ B p (0, 1)

def pairCompactFamily (B : ℝ × ℝ → ℝ) (r : ℝ) (y : ℝ) : IntervalFunctions r :=
  ContinuousMap.mkD (fun x : Icc (-r) r => B (x, y)) 0

theorem pairRectangle_isOpen (R a b : ℝ) : IsOpen (pairRectangle R a b) :=
  isOpen_Ioo.prod isOpen_Ioo

theorem exists_compact_time_interval {R x : ℝ} (hx : x ∈ Ioo (-R) R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ x ∈ Ioo (-r) r := by
  have hxa : |x| < R := abs_lt.mpr hx
  refine ⟨(|x| + R) / 2, ?_, ?_, ?_⟩
  · nlinarith [abs_nonneg x]
  · linarith
  · apply abs_lt.mp
    linarith

theorem pairCompactFamily_joint_continuous {B : ℝ × ℝ → ℝ} {R a b r : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) (hrR : r < R) :
    ContinuousOn (fun p : ℝ × Icc (-r) r => B (p.2, p.1))
      (Ioo a b ×ˢ (univ : Set (Icc (-r) r))) := by
  exact hB.comp (by fun_prop)
    (fun p hp => ⟨⟨(neg_lt_neg hrR).trans_le p.2.2.1,
      p.2.2.2.trans_lt hrR⟩, hp.1⟩)

theorem pairCompactFamily_continuousOn {B : ℝ × ℝ → ℝ} {R a b r : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) (hrR : r < R) :
    ContinuousOn (pairCompactFamily B r) (Ioo a b) :=
  ContinuousMap.continuousOn_mkD_of_uncurry _ 0 (pairCompactFamily_joint_continuous hB hrR)

theorem pairCompactFamily_apply {B : ℝ × ℝ → ℝ} {R a b r y : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) (hrR : r < R)
    (hy : y ∈ Ioo a b) (x : Icc (-r) r) : pairCompactFamily B r y x = B (x, y) := by
  have hc : Continuous (fun t : Icc (-r) r => B (t, y)) :=
    (pairCompactFamily_joint_continuous hB hrR).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hy, mem_univ _⟩)
  unfold pairCompactFamily
  rw [ContinuousMap.mkD_of_continuous hc]
  rfl

theorem pairPrimitive_eq_clamped {B : ℝ × ℝ → ℝ} {R a b r x y : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) (hr : 0 < r) (hrR : r < R)
    (hx : x ∈ Ioo (-r) r) (hy : y ∈ Ioo a b) :
    pairPrimitive B (x, y) =
      intervalExtension r hr (primitiveCLM r hr (pairCompactFamily B r y)) x := by
  rw [intervalExtension_apply_of_mem r hr _ ⟨hx.1.le, hx.2.le⟩, primitiveCLM_apply]
  unfold pairPrimitive
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (-r) r :=
    uIcc_subset_Icc ⟨by linarith, hr.le⟩ ⟨hx.1.le, hx.2.le⟩ ht
  rw [intervalExtension_apply_of_mem r hr _ ht', pairCompactFamily_apply hB hrR hy]

theorem pairPartialY_contDiffOn {B : ℝ × ℝ → ℝ} {R a b : ℝ} (n : ℕ)
    (hB : ContDiffOn ℝ (n + 1 : ℕ) B (pairRectangle R a b)) :
    ContDiffOn ℝ n (pairPartialY B) (pairRectangle R a b) := by
  have hd : ContDiffOn ℝ n (fderiv ℝ B) (pairRectangle R a b) :=
    hB.fderiv_of_isOpen (pairRectangle_isOpen R a b) (by simp)
  exact hd.clm_apply contDiffOn_const

theorem pairCompactFamily_hasDerivAt {B : ℝ × ℝ → ℝ} {R a b r y : ℝ}
    (hB : ContDiffOn ℝ 1 B (pairRectangle R a b)) (hrR : r < R) (hy : y ∈ Ioo a b) :
    HasDerivAt (pairCompactFamily B r) (pairCompactFamily (pairPartialY B) r y) y := by
  have hP : ContinuousOn (pairPartialY B) (pairRectangle R a b) :=
    (pairPartialY_contDiffOn 0 hB).continuousOn
  apply hasDerivAt_continuousMap_of_eval (pairCompactFamily_continuousOn hP hrR) _ hy
  intro u hu x
  have hx : (x : ℝ) ∈ Ioo (-R) R :=
    ⟨(neg_lt_neg hrR).trans_le x.2.1, x.2.2.trans_lt hrR⟩
  have hxu : ((x : ℝ), u) ∈ pairRectangle R a b := ⟨hx, hu⟩
  have hd := ((hB.contDiffAt ((pairRectangle_isOpen R a b).mem_nhds hxu)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hs : HasDerivAt (fun v : ℝ => ((x : ℝ), v)) (0, 1) u :=
    (hasDerivAt_const u (x : ℝ)).prodMk (hasDerivAt_id u)
  have hpoint : HasDerivAt (fun v => B (x, v)) (pairPartialY B (x, u)) u :=
    hd.comp_hasDerivAt u hs
  rw [pairCompactFamily_apply hP hrR hu x]
  apply hpoint.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact pairCompactFamily_apply hB.continuousOn hrR hv x

theorem pairPrimitive_hasDerivAt_y {B : ℝ × ℝ → ℝ} {R a b x y : ℝ}
    (hB : ContDiffOn ℝ 1 B (pairRectangle R a b))
    (hx : x ∈ Ioo (-R) R) (hy : y ∈ Ioo a b) :
    HasDerivAt (fun v => pairPrimitive B (x, v)) (pairPrimitive (pairPartialY B) (x, y)) y := by
  obtain ⟨r, hr, hrR, hxr⟩ := exists_compact_time_interval hx
  have hP : ContinuousOn (pairPartialY B) (pairRectangle R a b) :=
    (pairPartialY_contDiffOn 0 hB).continuousOn
  have hFB := pairCompactFamily_hasDerivAt hB hrR hy
  have hPB := (primitiveCLM r hr).hasFDerivAt.comp_hasDerivAt y hFB
  have hd := intervalExtension_family_hasDerivAt r hr hPB x
  rw [← pairPrimitive_eq_clamped hP hr hrR hxr hy] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hy] with v hv
  exact pairPrimitive_eq_clamped hB.continuousOn hr hrR hxr hv

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def solvedDarbouxQ (g : MetricField) (p : Coord) (b c : ℝ) (u : Coord) : ℝ :=
  jetConnection g p 1 1 u + jetNumerator g p b u / jetXX g p c u

theorem jetConnection_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (i j : Fin 2) (u : Coord) :
    jetConnection (swappedMetric g) p i j (coordinateSwap u) =
      jetConnection g (coordinateSwap p) (swapCoordinateIndex i) (swapCoordinateIndex j) u := by
  simp only [jetConnection, christoffel_swappedMetric hg hU hp,
    coordinateSwap_apply, Fin.sum_univ_two, swapCoordinateIndex_zero, swapCoordinateIndex_one]
  ring

theorem jetMixed_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (b : ℝ) (u : Coord) :
    jetMixed (swappedMetric g) p b (coordinateSwap u) =
      jetMixed g (coordinateSwap p) b u := by
  have hs (k : Fin 2) : christoffel g k 1 0 (coordinateSwap p) =
      christoffel g k 0 1 (coordinateSwap p) := christoffel_lower_symm hg hU hp k 1 0
  rw [jetMixed, jetConnection_swappedMetric hg hU hp]
  simp only [swapCoordinateIndex_zero, swapCoordinateIndex_one]
  simp only [jetConnection, hs, jetMixed]

theorem jetYY_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (c : ℝ) (u : Coord) :
    jetYY (swappedMetric g) p c (coordinateSwap u) =
      jetXX g (coordinateSwap p) c u := by
  rw [jetYY, jetConnection_swappedMetric hg hU hp]
  rfl

theorem jetEnergy_swappedMetric (g : MetricField) (p u : Coord) :
    jetEnergy (swappedMetric g) p (coordinateSwap u) =
      jetEnergy g (coordinateSwap p) u := by
  simp only [jetEnergy, swappedMetric_det, swappedMetric_apply, coordinateSwap_apply,
    swapCoordinateIndex_zero, swapCoordinateIndex_one]
  ring

theorem jetNumerator_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (b : ℝ) (u : Coord) :
    jetNumerator (swappedMetric g) p b (coordinateSwap u) =
      jetNumerator g (coordinateSwap p) b u := by
  rw [jetNumerator, jetMixed_swappedMetric hg hU hp,
    gaussianCurvature_swappedMetric hg hU hp, jetEnergy_swappedMetric]
  rfl

theorem solvedDarboux_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (b c : ℝ) (u : Coord) :
    solvedDarboux (swappedMetric g) p b c (coordinateSwap u) =
      solvedDarbouxQ g (coordinateSwap p) b c u := by
  rw [solvedDarboux, jetConnection_swappedMetric hg hU hp,
    jetNumerator_swappedMetric hg hU hp, jetYY_swappedMetric hg hU hp]
  rfl

theorem solvedDarbouxQ_eq_swappedP {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ U) (b c : ℝ) (u : Coord) :
    solvedDarbouxQ g p b c u =
      solvedDarboux (swappedMetric g) (coordinateSwap p) b c (coordinateSwap u) := by
  simpa only [coordinateSwap_involutive] using
    (solvedDarboux_swappedMetric hg hU (p := coordinateSwap p) (by simpa using hp) b c u).symm

theorem jetXX_at_height (g : MetricField) (p : Coord) (z : Coord → ℝ) :
    jetXX g p (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p) =
      covHessian g z p 0 0 := rfl

theorem solvedDarbouxQ_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    coordPartial 1 (coordPartial 1 z) p =
      solvedDarbouxQ g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p) := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  have hsolve : covHessian g z p 1 1 =
      ((covHessian g z p 0 1) ^ 2 + gaussianCurvature g p * heightEnergy g z p) /
        covHessian g z p 0 0 := by
    apply (eq_div_iff hxx).2
    nlinarith [hdet]
  change coordPartial 1 (coordPartial 1 z) p -
    jetConnection g p 1 1 (fun i => coordPartial i z p) = _ at hsolve
  rw [solvedDarbouxQ, jetNumerator, jetMixed_at_height, jetXX_at_height,
    jetEnergy_at_height hg hp z]
  linarith [hsolve]

theorem darbouxDet_of_solvedQ_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0)
    (hQ : coordPartial 1 (coordPartial 1 z) p =
      solvedDarbouxQ g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p)) :
    (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p := by
  rw [solvedDarbouxQ, jetNumerator, jetMixed_at_height, jetXX_at_height,
    jetEnergy_at_height hg hp z] at hQ
  have hsolve : covHessian g z p 1 1 =
      ((covHessian g z p 0 1) ^ 2 + gaussianCurvature g p * heightEnergy g z p) /
        covHessian g z p 0 0 := by
    change coordPartial 1 (coordPartial 1 z) p -
      jetConnection g p 1 1 (fun i => coordPartial i z p) = _
    linarith [hQ]
  have hmul := (eq_div_iff hxx).1 hsolve
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    nlinarith [hmul]
  simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hdet

theorem darbouxDet_iff_solvedQ_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p ↔
      coordPartial 1 (coordPartial 1 z) p =
        solvedDarbouxQ g p (coordPartial 0 (coordPartial 1 z) p)
          (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p) :=
  ⟨solvedDarbouxQ_at_height hg hU hz hp hxx,
    darbouxDet_of_solvedQ_at_height hg hU hz hp hxx⟩

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Flow

variable {B : Coord → ℝ} {R a b : ℝ}

theorem coefficient_pair_contDiffOn
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => B (coordinatePoint p.1 p.2)) (pairRectangle R a b) := by
  have hpoint : ContDiff ℝ ∞ (fun p : ℝ × ℝ => coordinatePoint p.1 p.2) := by
    unfold coordinatePoint
    fun_prop
  exact hB.comp hpoint.contDiffOn (fun p hp => point_mem_rectangle hp.1 hp.2)

theorem coefficient_pairPartialY
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    {x y : ℝ} (hx : x ∈ Ioo (-R) R) (hy : y ∈ Ioo a b) :
    pairPartialY (fun p : ℝ × ℝ => B (coordinatePoint p.1 p.2)) (x, y) =
      coordPartial 1 B (coordinatePoint x y) := by
  have hdB : DifferentiableAt ℝ B (coordinatePoint x y) :=
    ((hB.contDiffAt ((coordinateRectangle_isOpen R a b).mem_nhds
      (point_mem_rectangle hx hy))).differentiableAt (by simp))
  have hdPair : DifferentiableAt ℝ (fun p : ℝ × ℝ => B (coordinatePoint p.1 p.2)) (x, y) :=
    (((coefficient_pair_contDiffOn hB).contDiffAt
      ((pairRectangle_isOpen R a b).mem_nhds ⟨hx, hy⟩)).differentiableAt (by simp))
  have hcoord : HasDerivAt (fun t => B (coordinatePoint x t))
      (coordPartial 1 B (coordinatePoint x y)) y :=
    hdB.hasFDerivAt.comp_hasDerivAt y (coordinatePoint_hasDerivAt_y x y)
  have hpair : HasDerivAt (fun t => B (coordinatePoint x t))
      (pairPartialY (fun p : ℝ × ℝ => B (coordinatePoint p.1 p.2)) (x, y)) y :=
    hdPair.hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  exact hpair.unique hcoord

theorem coordinatePrimitive_partial_s
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b) :
    coordPartial 1 (coordinatePrimitive B) p =
      ∫ t in 0..p 0, coordPartial 1 B (coordinatePoint t (p 1)) := by
  have hpairC1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => B (coordinatePoint q.1 q.2))
      (pairRectangle R a b) := (coefficient_pair_contDiffOn hB).of_le (by simp)
  have hftc := pairPrimitive_hasDerivAt_y hpairC1 hp.1 hp.2
  have hseg : uIcc 0 (p 0) ⊆ Ioo (-R) R := by
    have hz : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
    intro t ht
    exact ⟨lt_of_lt_of_le (lt_min hz.1 hp.1.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hz.2 hp.1.2)⟩
  have he : pairPrimitive
      (pairPartialY (fun q : ℝ × ℝ => B (coordinatePoint q.1 q.2))) (p 0, p 1) =
      ∫ t in 0..p 0, coordPartial 1 B (coordinatePoint t (p 1)) := by
    unfold pairPrimitive
    apply intervalIntegral.integral_congr
    intro t ht
    exact coefficient_pairPartialY hB (hseg ht) hp.2
  rw [he] at hftc
  have hftc' : HasDerivAt (fun s => coordinatePrimitive B (coordinatePoint (p 0) s))
      (∫ t in 0..p 0, coordPartial 1 B (coordinatePoint t (p 1))) (p 1) := by
    simpa [pairPrimitive, coordinatePrimitive, coordinatePoint] using hftc
  have hdI : DifferentiableAt ℝ (coordinatePrimitive B) (coordinatePoint (p 0) (p 1)) := by
    rw [point_eta]
    exact ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by simp)
  have hchain := hdI.hasFDerivAt.comp_hasDerivAt (p 1) (coordinatePoint_hasDerivAt_y (p 0) (p 1))
  have hcoord : HasDerivAt (fun s => coordinatePrimitive B (coordinatePoint (p 0) s))
      (coordPartial 1 (coordinatePrimitive B) p) (p 1) := by
    simpa only [point_eta, Function.comp_def, coordPartial] using hchain
  exact hcoord.unique hftc'

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

universe u
namespace SmoothLocal.Analytic
open SmoothLocal.Geometry

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def compactParameterIntegral (H : Coord × ℝ → F) (p : Coord) : F :=
  ∫ s in Icc (0 : ℝ) 1, H (p,s)

def compactParameterPartial (H : Coord × ℝ → F) (q : Coord × ℝ) : Coord →L[ℝ] F :=
  (fderiv ℝ H q).comp (ContinuousLinearMap.inl ℝ Coord ℝ)

omit [NormedSpace ℝ F] [CompleteSpace F] in
theorem parameter_slice_continuousOn
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContinuousOn H D) (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D)
    {p : Coord} (hp : p ∈ U) : ContinuousOn (fun s => H (p,s)) (Icc (0 : ℝ) 1) :=
  hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hs => hUD ⟨hp,hs⟩)

omit [NormedSpace ℝ F] [CompleteSpace F] in
theorem exists_local_parameter_norm_bound
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContinuousOn H D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) {p : Coord} (hp : p ∈ U) :
    ∃ e B : ℝ, 0 < e ∧ 0 ≤ B ∧ Metric.ball p e ⊆ U ∧
      ∀ x ∈ Metric.ball p e, ∀ s ∈ Icc (0 : ℝ) 1, ‖H (x,s)‖ ≤ B := by
  obtain ⟨e,he,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let K := Metric.closedBall p (e/2) ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := (isCompact_closedBall p (e/2)).prod isCompact_Icc
  have hKD : K ⊆ D := by
    intro q hq
    exact hUD ⟨hball (Metric.closedBall_subset_ball (half_lt_self he) hq.1),hq.2⟩
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (hH.mono hKD)
  refine ⟨e/2,max B 0,half_pos he,le_max_right _ _,?_,?_⟩
  · intro x hx
    exact hball ((Metric.ball_subset_ball (half_le_self he.le)) hx)
  · intro x hx s hs
    exact (hB (x,s) ⟨Metric.ball_subset_closedBall hx,hs⟩).trans (le_max_left _ _)

omit [CompleteSpace F] in
theorem compactParameterIntegral_continuousOn
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContinuousOn H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) : ContinuousOn (compactParameterIntegral H) U := by
  intro p hp
  obtain ⟨e,B,he,hB,hball,hbound⟩ := exists_local_parameter_norm_bound hH hU hUD hp
  have hmeas : ∀ᶠ x in 𝓝 p, AEStronglyMeasurable (fun s => H (x,s))
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact ((parameter_slice_continuousOn hH hUD hx).integrableOn_compact isCompact_Icc).aestronglyMeasurable
  have hdom : ∀ᶠ x in 𝓝 p, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), ‖H (x,s)‖ ≤ B := by
    filter_upwards [Metric.ball_mem_nhds p he] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hbound x hx s hs
  have hint : Integrable (fun _ : ℝ => B) (volume.restrict (Icc (0 : ℝ) 1)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hpoint : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), ContinuousAt (fun x => H (x,s)) p := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (hH.continuousAt (hD.mem_nhds (hUD ⟨hp,hs⟩))).comp
      (continuous_id.prodMk continuous_const).continuousAt
  exact (continuousAt_of_dominated hmeas hdom hint hpoint).continuousWithinAt

omit [CompleteSpace F] in
theorem compactParameterPartial_contDiffOn
    {H : Coord × ℝ → F} {D : Set (Coord × ℝ)} (hD : IsOpen D) (n : ℕ)
    (hH : ContDiffOn ℝ (n+1 : ℕ) H D) :
    ContDiffOn ℝ n (compactParameterPartial H) D := by
  have hd : ContDiffOn ℝ n (fderiv ℝ H) D := hH.fderiv_of_isOpen hD (by simp)
  exact hd.clm_comp contDiffOn_const

omit [CompleteSpace F] in
theorem compactParameter_slice_hasFDerivAt
    {H : Coord × ℝ → F} {D : Set (Coord × ℝ)} (hH : ContDiffOn ℝ 1 H D)
    (hD : IsOpen D) {p : Coord} {s : ℝ} (hp : (p,s) ∈ D) :
    HasFDerivAt (fun x => H (x,s)) (compactParameterPartial H (p,s)) p := by
  have hd := ((hH.contDiffAt (hD.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt
  have hi : HasFDerivAt (fun x : Coord => (x,s)) (ContinuousLinearMap.inl ℝ Coord ℝ) p :=
    hasFDerivAt_prodMk_left p s
  exact hd.comp p hi

omit [CompleteSpace F] in
theorem compactParameterIntegral_hasFDerivAt
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContDiffOn ℝ 1 H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) {p : Coord} (hp : p ∈ U) :
    HasFDerivAt (compactParameterIntegral H)
      (compactParameterIntegral (compactParameterPartial H) p) p := by
  have hpart : ContinuousOn (compactParameterPartial H) D :=
    (compactParameterPartial_contDiffOn hD 0 hH).continuousOn
  obtain ⟨e,B,he,hB,hball,hbound⟩ := exists_local_parameter_norm_bound hpart hU hUD hp
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Icc (0 : ℝ) 1)) (bound := fun _ => B)
    (s := Metric.ball p e) (F' := fun x s => compactParameterPartial H (x,s))
    (Metric.ball_mem_nhds p he)
  · filter_upwards [hU.mem_nhds hp] with x hx
    exact ((parameter_slice_continuousOn hH.continuousOn hUD hx).integrableOn_compact isCompact_Icc).aestronglyMeasurable
  · exact (parameter_slice_continuousOn hH.continuousOn hUD hp).integrableOn_compact isCompact_Icc
  · exact ((parameter_slice_continuousOn hpart hUD hp).integrableOn_compact isCompact_Icc).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    intro x hx
    exact hbound x hx s hs
  · exact integrableOn_const isCompact_Icc.measure_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    intro x hx
    exact compactParameter_slice_hasFDerivAt hH hD (hUD ⟨hball hx,hs⟩)

theorem compactParameterIntegral_contDiffOn_finite (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)},
      ContDiffOn ℝ n H D → IsOpen D → IsOpen U →
      U ×ˢ Icc (0 : ℝ) 1 ⊆ D → ContDiffOn ℝ n (compactParameterIntegral H) U := by
  induction n with
  | zero =>
    intro F _ _ _ H U D hH hD hU hUD
    simpa only [Nat.cast_zero,contDiffOn_zero] using
      compactParameterIntegral_continuousOn hH.continuousOn hD hU hUD
  | succ n ih =>
    intro F _ _ _ H U D hH hD hU hUD
    have hH1 : ContDiffOn ℝ 1 H D := hH.of_le (by exact_mod_cast (show 1 ≤ n+1 by omega))
    have hd (p : Coord) (hp : p ∈ U) := compactParameterIntegral_hasFDerivAt hH1 hD hU hUD hp
    have hpart : ContDiffOn ℝ n (compactParameterPartial H) D :=
      compactParameterPartial_contDiffOn hD n hH
    have hmeanPart : ContDiffOn ℝ n (compactParameterIntegral (compactParameterPartial H)) U :=
      ih hpart hD hU hUD
    have hs : ContDiffOn ℝ ((n : ℕ∞ω)+1) (compactParameterIntegral H) U := by
      rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun p hp => (hd p hp).differentiableAt.differentiableWithinAt,by simp,?_⟩
      exact hmeanPart.congr (fun p hp => (hd p hp).fderiv)
    simpa only [Nat.cast_add,Nat.cast_one] using hs

theorem compactParameterIntegral_contDiffOn
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContDiffOn ℝ ∞ H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) :
    ContDiffOn ℝ ∞ (compactParameterIntegral H) U :=
  contDiffOn_infty.mpr (fun n => compactParameterIntegral_contDiffOn_finite n
    (hH.of_le (WithTop.coe_le_coe.mpr le_top)) hD hU hUD)

end SmoothLocal.Analytic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def qToPStateLinear : DarbouxState →ₗ[ℝ] DarbouxState where
  toFun := qToPState
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def qToPStateCLM : DarbouxState →L[ℝ] DarbouxState :=
  LinearMap.toContinuousLinearMap qToPStateLinear

@[simp] theorem qToPStateCLM_apply (w : DarbouxState) : qToPStateCLM w = qToPState w := rfl

@[simp] theorem qToPStateIndex_involutive (i : Fin 6) :
    qToPStateIndex (qToPStateIndex i) = i := by
  fin_cases i <;> rfl

@[simp] theorem qToPState_involutive (w : DarbouxState) : qToPState (qToPState w) = w := by
  ext i
  exact congrArg w (qToPStateIndex_involutive i)

theorem qToPState_contDiff : ContDiff ℝ ∞ qToPState := qToPStateCLM.contDiff

@[simp] theorem statePoint_qToPState (w : DarbouxState) :
    statePoint (qToPState w) = coordinateSwap (statePoint w) := by
  ext i
  fin_cases i <;> simp [statePoint, qToPState, qToPStateIndex]

@[simp] theorem stateGradient_qToPState (w : DarbouxState) :
    stateGradient (qToPState w) = coordinateSwap (stateGradient w) := by
  ext i
  fin_cases i <;> simp [stateGradient, qToPState, qToPStateIndex]

@[simp] theorem qToPState_four (w : DarbouxState) : qToPState w 4 = w 4 := rfl
@[simp] theorem qToPState_five (w : DarbouxState) : qToPState w 5 = w 5 := rfl

def darbouxQStateDomain (g : MetricField) (U : Set Coord) : Set DarbouxState :=
  {w | statePoint w ∈ U ∧ stateQDenominator g w ≠ 0}

theorem stateDenominator_qToPState {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    stateDenominator (swappedMetric g) (qToPState w) = stateQDenominator g w := by
  unfold stateDenominator
  rw [statePoint_qToPState, stateGradient_qToPState, qToPState_five]
  simpa only [stateQDenominator, coordinateSwap_involutive] using
    (jetYY_swappedMetric hg hU (p := coordinateSwap (statePoint w))
      (by simpa using hw) (w 5) (stateGradient w))

theorem sixVariableQ_explicit {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    sixVariableQ g w =
      solvedDarbouxQ g (statePoint w) (w 4) (w 5) (stateGradient w) := by
  unfold sixVariableQ sixVariableP
  simp only [Function.comp_apply, statePoint_qToPState, stateGradient_qToPState,
    qToPState_four, qToPState_five]
  exact (solvedDarbouxQ_eq_swappedP hg hU hw (w 4) (w 5) (stateGradient w)).symm

theorem darbouxQStateDomain_eq_preimage {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    darbouxQStateDomain g U =
      qToPState ⁻¹' darbouxStateDomain (swappedMetric g) (coordinateSwap ⁻¹' U) := by
  ext w
  constructor
  · intro hw
    refine ⟨?_, ?_⟩
    · simpa only [Set.mem_preimage, statePoint_qToPState, coordinateSwap_involutive] using hw.1
    · simpa only [stateDenominator_qToPState hg hU hw.1] using hw.2
  · intro hw
    have hp : statePoint w ∈ U := by
      simpa only [Set.mem_preimage, statePoint_qToPState, coordinateSwap_involutive] using hw.1
    exact ⟨hp, by simpa only [stateDenominator_qToPState hg hU hp] using hw.2⟩

theorem qToPState_mem_domain {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    qToPState w ∈ darbouxStateDomain (swappedMetric g) (coordinateSwap ⁻¹' U) := by
  simpa only [darbouxQStateDomain_eq_preimage hg hU, Set.mem_preimage] using hw

theorem darbouxQStateDomain_isOpen {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) : IsOpen (darbouxQStateDomain g U) := by
  rw [darbouxQStateDomain_eq_preimage hg hU]
  exact (darbouxStateDomain_isOpen (swappedMetric_smoothPositive hg)
    (coordinateSwap_preimage_isOpen hU)).preimage qToPState_contDiff.continuous

theorem sixVariableQ_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (sixVariableQ g) (darbouxQStateDomain g U) :=
  (sixVariableP_contDiffOn (swappedMetric_smoothPositive hg)
    (coordinateSwap_preimage_isOpen hU)).comp qToPState_contDiff.contDiffOn
      (fun _ hw => qToPState_mem_domain hg hU hw)

theorem statePoint_qSolutionJet (z : Coord → ℝ) (p : Coord) :
    statePoint (qSolutionJet z p) = p := by
  ext i
  fin_cases i <;> rfl

theorem stateGradient_qSolutionJet (z : Coord → ℝ) (p : Coord) :
    stateGradient (qSolutionJet z p) = fun i => coordPartial i z p := by
  ext i
  fin_cases i <;> rfl

theorem stateQDenominator_qSolutionJet (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    stateQDenominator g (qSolutionJet z p) = covHessian g z p 0 0 := by
  unfold stateQDenominator
  rw [statePoint_qSolutionJet, stateGradient_qSolutionJet]
  exact jetXX_at_height g p z

theorem qSolutionJet_mem_domain {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    qSolutionJet z p ∈ darbouxQStateDomain g U := by
  constructor
  · simpa only [statePoint_qSolutionJet] using hp
  · simpa only [stateQDenominator_qSolutionJet] using hxx

theorem darbouxDet_iff_sixVariableQ {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p ↔
      coordPartial 1 (coordPartial 1 z) p = sixVariableQ g (qSolutionJet z p) := by
  rw [sixVariableQ_explicit hg hU (by simpa only [statePoint_qSolutionJet] using hp),
    statePoint_qSolutionJet, stateGradient_qSolutionJet]
  exact darbouxDet_iff_solvedQ_at_height hg hU hz hp hxx

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

theorem inwardLeft_hasDerivAt (x0 theta0 speed theta : ℝ) :
    HasDerivAt (inwardLeft x0 theta0 speed) speed theta := by
  unfold inwardLeft
  simpa only [inwardLeft, mul_one, id_eq] using
    (((hasDerivAt_id theta).sub_const theta0).const_mul speed).const_add x0

theorem inwardRight_hasDerivAt (x0 theta0 speed theta : ℝ) :
    HasDerivAt (inwardRight x0 theta0 speed) (-speed) theta := by
  unfold inwardRight
  simpa only [inwardRight, mul_one, zero_sub, id_eq, Pi.sub_def] using
    (hasDerivAt_const theta x0).sub
      (((hasDerivAt_id theta).sub_const theta0).const_mul speed)

theorem movingPoint_hasDerivAt {x : ℝ → ℝ} {dx theta : ℝ}
    (hx : HasDerivAt x dx theta) :
    HasDerivAt (fun t => coordinatePoint (x t) t)
      (dx • Pi.single 0 (1 : ℝ) + Pi.single 1 (1 : ℝ) : Coord) theta := by
  simpa only [coordinatePoint, one_smul, id_eq, Pi.add_def] using
    (hx.smul_const (Pi.single 0 (1 : ℝ) : Coord)).add
      ((hasDerivAt_id theta).smul_const (Pi.single 1 (1 : ℝ) : Coord))

theorem slice_intervalIntegrable
    {f : Coord → ℝ} {radius lo hi xl xr theta : ℝ}
    (hf : ContinuousOn f (coordinateRectangle radius lo hi))
    (hxl : xl ∈ Ioo (-radius) radius) (hxr : xr ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    IntervalIntegrable (fun xi => f (coordinatePoint xi theta)) volume xl xr := by
  have hc : ContinuousOn (fun xi => f (coordinatePoint xi theta)) (Ioo (-radius) radius) :=
    hf.comp (by unfold coordinatePoint; fun_prop) (fun xi hxi => point_mem_rectangle hxi htheta)
  exact (hc.mono (fun xi hxi =>
    ⟨lt_of_lt_of_le (lt_min hxl.1 hxr.1) hxi.1,
      lt_of_le_of_lt hxi.2 (max_lt hxl.2 hxr.2)⟩)).intervalIntegrable

theorem movingIntervalIntegral_eq_primitive
    {f : Coord → ℝ} {left right : ℝ → ℝ} {radius lo hi theta : ℝ}
    (hf : ContinuousOn f (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hl : left theta ∈ Ioo (-radius) radius) (hr : right theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    movingIntervalIntegral left right f theta =
      coordinatePrimitive f (coordinatePoint (right theta) theta) -
      coordinatePrimitive f (coordinatePoint (left theta) theta) := by
  have h0 : (0 : ℝ) ∈ Ioo (-radius) radius := ⟨by linarith, hradius⟩
  have hrI := slice_intervalIntegrable hf h0 hr htheta
  have hlI := slice_intervalIntegrable hf h0 hl htheta
  simpa [movingIntervalIntegral, coordinatePrimitive, coordinatePoint] using
    (intervalIntegral.integral_interval_sub_left hrI hlI).symm

theorem movingPrimitive_hasDerivAt
    {f : Coord → ℝ} {x : ℝ → ℝ} {radius lo hi theta dx : ℝ}
    (hf : ContDiffOn ℝ ∞ f (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hx : HasDerivAt x dx theta) (hxt : x theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    HasDerivAt (fun t => coordinatePrimitive f (coordinatePoint (x t) t))
      (dx * f (coordinatePoint (x theta) theta) +
        ∫ xi in 0..x theta, coordPartial 1 f (coordinatePoint xi theta)) theta := by
  have hp := point_mem_rectangle hxt htheta
  have hd : DifferentiableAt ℝ (coordinatePrimitive f) (coordinatePoint (x theta) theta) :=
    ((coordinatePrimitive_contDiffOn hf).contDiffAt
      ((coordinateRectangle_isOpen radius lo hi).mem_nhds hp)).differentiableAt (by simp)
  have hchain := HasFDerivAt.comp_hasDerivAt theta
    (f := fun t => coordinatePoint (x t) t) hd.hasFDerivAt
    (movingPoint_hasDerivAt (x := x) hx)
  have ht := coordinatePrimitive_partial_t hf hradius hp
  have hs := coordinatePrimitive_partial_s hf hradius hp
  simp only [coordPartial] at ht hs
  simp only [map_add, map_smul,
    smul_eq_mul, ht, hs] at hchain
  simpa [coordinatePoint, coordPartial, Function.comp_def] using hchain

theorem movingIntervalIntegral_hasDerivAt
    {f : Coord → ℝ} {left right : ℝ → ℝ} {radius lo hi theta dl dr : ℝ}
    (hf : ContDiffOn ℝ ∞ f (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hl : HasDerivAt left dl theta) (hr : HasDerivAt right dr theta)
    (hlt : left theta ∈ Ioo (-radius) radius)
    (hrt : right theta ∈ Ioo (-radius) radius) (htheta : theta ∈ Ioo lo hi) :
    HasDerivAt (movingIntervalIntegral left right f)
      ((∫ xi in left theta..right theta, coordPartial 1 f (coordinatePoint xi theta)) +
        dr * f (coordinatePoint (right theta) theta) -
        dl * f (coordinatePoint (left theta) theta)) theta := by
  have hright := movingPrimitive_hasDerivAt hf hradius hr hrt htheta
  have hleft := movingPrimitive_hasDerivAt hf hradius hl hlt htheta
  have hdiff := hright.sub hleft
  have h0 : (0 : ℝ) ∈ Ioo (-radius) radius := ⟨by linarith, hradius⟩
  have hf1 := (partial_contDiffOn hf (coordinateRectangle_isOpen radius lo hi) 1).continuousOn
  have hIsub := intervalIntegral.integral_interval_sub_left
    (slice_intervalIntegrable hf1 h0 hrt htheta)
    (slice_intervalIntegrable hf1 h0 hlt htheta)
  have he :
      (dr * f (coordinatePoint (right theta) theta) +
        ∫ xi in 0..right theta, coordPartial 1 f (coordinatePoint xi theta)) -
      (dl * f (coordinatePoint (left theta) theta) +
        ∫ xi in 0..left theta, coordPartial 1 f (coordinatePoint xi theta)) =
      (∫ xi in left theta..right theta, coordPartial 1 f (coordinatePoint xi theta)) +
        dr * f (coordinatePoint (right theta) theta) -
        dl * f (coordinatePoint (left theta) theta) := by linarith
  rw [he] at hdiff
  apply hdiff.congr_of_eventuallyEq
  filter_upwards [hl.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hlt),
    hr.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hrt),
    isOpen_Ioo.mem_nhds htheta] with t hlt' hrt' ht'
  exact movingIntervalIntegral_eq_primitive hf.continuousOn hradius hlt' hrt' ht'

theorem inwardIntervalIntegral_hasDerivAt
    {f : Coord → ℝ} {radius lo hi xl xr theta0 speed theta : ℝ}
    (hf : ContDiffOn ℝ ∞ f (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hl : inwardLeft xl theta0 speed theta ∈ Ioo (-radius) radius)
    (hr : inwardRight xr theta0 speed theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    HasDerivAt
      (movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed) f)
      ((∫ xi in inwardLeft xl theta0 speed theta..inwardRight xr theta0 speed theta,
          coordPartial 1 f (coordinatePoint xi theta)) -
        speed * (f (coordinatePoint (inwardRight xr theta0 speed theta) theta) +
          f (coordinatePoint (inwardLeft xl theta0 speed theta) theta))) theta := by
  convert movingIntervalIntegral_hasDerivAt hf hradius
    (inwardLeft_hasDerivAt xl theta0 speed theta)
    (inwardRight_hasDerivAt xr theta0 speed theta) hl hr htheta using 1
  ring

theorem slice_integral_partial_xi
    {f : Coord → ℝ} {radius lo hi xl xr theta : ℝ}
    (hf : ContDiffOn ℝ ∞ f (coordinateRectangle radius lo hi))
    (hxl : xl ∈ Ioo (-radius) radius) (hxr : xr ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    (∫ xi in xl..xr, coordPartial 0 f (coordinatePoint xi theta)) =
      f (coordinatePoint xr theta) - f (coordinatePoint xl theta) := by
  have hmem {xi : ℝ} (hxi : xi ∈ uIcc xl xr) :
      coordinatePoint xi theta ∈ coordinateRectangle radius lo hi :=
    point_mem_rectangle
      ⟨lt_of_lt_of_le (lt_min hxl.1 hxr.1) hxi.1,
        lt_of_le_of_lt hxi.2 (max_lt hxl.2 hxr.2)⟩ htheta
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro xi hxi
    have hd : DifferentiableAt ℝ f (coordinatePoint xi theta) :=
      (hf.contDiffAt ((coordinateRectangle_isOpen radius lo hi).mem_nhds
        (hmem hxi))).differentiableAt (by simp)
    exact hd.hasFDerivAt.comp_hasDerivAt xi (point_hasDerivAt_t xi theta)
  · exact slice_intervalIntegrable
      (partial_contDiffOn hf (coordinateRectangle_isOpen radius lo hi) 0).continuousOn
      hxl hxr htheta

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def stateBaseCompact (S : Set Coord) (M : ℝ) : Set DarbouxState :=
  (statePoint ⁻¹' S) ∩ Icc (fun _ => -M) (fun _ => M)

theorem stateBaseCompact_isCompact {S : Set Coord} (hS : IsCompact S) (M : ℝ) :
    IsCompact (stateBaseCompact S M) :=
  isCompact_Icc.inter_left (hS.isClosed.preimage statePoint_contDiff.continuous)

theorem stateSegment_coord_bound {w0 w1 : DarbouxState} {sigma M : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ i, |w0 i| ≤ M) (h1 : ∀ i, |w1 i| ≤ M) (i : Fin 6) :
    |stateSegment w0 w1 sigma i| ≤ M := by
  change |(1 - sigma) * w0 i + sigma * w1 i| ≤ M
  calc
    _ ≤ |(1 - sigma) * w0 i| + |sigma * w1 i| := abs_add_le _ _
    _ = (1 - sigma) * |w0 i| + sigma * |w1 i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2), abs_of_nonneg hs.1]
    _ ≤ (1 - sigma) * M + sigma * M :=
      add_le_add (mul_le_mul_of_nonneg_left (h0 i) (sub_nonneg.mpr hs.2))
        (mul_le_mul_of_nonneg_left (h1 i) hs.1)
    _ = M := by ring

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem qFirstCoefficient_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (i : Fin 6) :
    ContDiffOn ℝ ∞ (qFirstCoefficient g i) (darbouxQStateDomain g U) :=
  ((sixVariableQ_contDiffOn hg hU).fderiv_of_isOpen
    (darbouxQStateDomain_isOpen hg hU) (by simp)).clm_apply contDiffOn_const

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

def movingEnergyRate (xl xr theta0 speed : ℝ) (P S bTheta bXi v R : Coord → ℝ)
    (theta : ℝ) : ℝ :=
  energyFlux P S v (coordinatePoint (inwardRight xr theta0 speed theta) theta) -
    energyFlux P S v (coordinatePoint (inwardLeft xl theta0 speed theta) theta) -
    speed * (energyDensity S v (coordinatePoint (inwardRight xr theta0 speed theta) theta) +
      energyDensity S v (coordinatePoint (inwardLeft xl theta0 speed theta) theta)) +
    movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
      (fun p => energyCoefficientError P S bTheta bXi v p + R p * coordPartial 1 v p) theta

theorem interval_product_abs_le_sqrt_squares
    {f g : ℝ → ℝ} {xl xr : ℝ} (hlr : xl ≤ xr)
    (hf : ContinuousOn f (Icc xl xr)) (hg : ContinuousOn g (Icc xl xr)) :
    |∫ x in xl..xr, f x * g x| ≤
      Real.sqrt (∫ x in xl..xr, f x ^ 2) * Real.sqrt (∫ x in xl..xr, g x ^ 2) := by
  have hf2 : MemLp f 2 (volume.restrict (Icc xl xr)) :=
    (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable measurableSet_Icc)).2
      ((hf.pow 2).integrableOn_compact isCompact_Icc)
  have hg2 : MemLp g 2 (volume.restrict (Icc xl xr)) :=
    (memLp_two_iff_integrable_sq (hg.aestronglyMeasurable measurableSet_Icc)).2
      ((hg.pow 2).integrableOn_compact isCompact_Icc)
  simpa only [intervalIntegral.integral_of_le hlr, restrict_Ioc_eq_restrict_Icc] using
    integral_product_abs_le_sqrt_squares hf2 hg2

variable {P S bTheta bXi v R : Coord → ℝ} {radius lo hi xl xr theta0 speed theta : ℝ}

theorem movingEnergy_nonneg
    (hlr : inwardLeft xl theta0 speed theta ≤ inwardRight xr theta0 speed theta)
    (hS : ∀ x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta),
      0 ≤ S (coordinatePoint x theta)) :
    0 ≤ movingEnergy xl xr theta0 speed S v theta := by
  exact intervalIntegral.integral_nonneg hlr (fun x hx => energyDensity_nonneg (hS x hx))

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace SmoothLocal.Hyperbolic

theorem regularized_sqrt_rate_le
    {E Ed force C eta : ℝ} (hE : 0 ≤ E) (hforce : 0 ≤ force) (hC : 0 ≤ C)
    (heta : 0 < eta) (hEd : Ed ≤ C * E + Real.sqrt (2 * E) * force) :
    Ed / (2 * Real.sqrt (E + eta)) ≤ C * Real.sqrt (E + eta) + force := by
  have hpos : 0 < E + eta := by linarith
  have hrootpos := Real.sqrt_pos.2 hpos
  have hsquare := Real.sq_sqrt hpos.le
  have hroot : Real.sqrt (2 * E) ≤ 2 * Real.sqrt (E + eta) := by
    apply Real.sqrt_le_iff.2
    constructor
    · positivity
    · nlinarith
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (E + eta))).2
  have hf := mul_le_mul_of_nonneg_right hroot hforce
  have hCE : C * E ≤ 2 * C * (E + eta) := by
    nlinarith [mul_nonneg hC hE, mul_nonneg hC heta.le]
  nlinarith

def regularizedWeightedEnergy (E : ℝ → ℝ) (C a eta : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-C * (t - a)) * Real.sqrt (E t + eta)

def regularizedWeightedRate (E Ed : ℝ → ℝ) (C a eta : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-C * (t - a)) *
    (Ed t / (2 * Real.sqrt (E t + eta)) - C * Real.sqrt (E t + eta))

theorem regularizedWeightedEnergy_hasDerivAt
    {E : ℝ → ℝ} {Ed C a eta t : ℝ} (hd : HasDerivAt E Ed t)
    (hE : 0 ≤ E t) (heta : 0 < eta) :
    HasDerivAt (regularizedWeightedEnergy E C a eta)
      (Real.exp (-C * (t - a)) *
        (Ed / (2 * Real.sqrt (E t + eta)) - C * Real.sqrt (E t + eta))) t := by
  have hroot := (hd.add_const eta).sqrt (by linarith : E t + eta ≠ 0)
  have he := (((hasDerivAt_id t).sub_const a).const_mul (-C)).exp
  have hh := he.mul hroot
  simp only [id_eq, mul_one] at hh
  unfold regularizedWeightedEnergy
  convert hh using 1 <;> try with_reducible_and_instances rfl
  first | rfl | ring

theorem regularizedWeightedRate_le
    {E Ed force : ℝ → ℝ} {C a eta t : ℝ} (hE : 0 ≤ E t)
    (hforce : 0 ≤ force t) (hC : 0 ≤ C) (heta : 0 < eta) (hat : a ≤ t)
    (hEd : Ed t ≤ C * E t + Real.sqrt (2 * E t) * force t) :
    regularizedWeightedRate E Ed C a eta t ≤ force t := by
  have hy := regularized_sqrt_rate_le hE hforce hC heta hEd
  have hfactor : Real.exp (-C * (t - a)) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    nlinarith
  have hfpos := (Real.exp_pos (-C * (t - a))).le
  have hmul := mul_le_mul_of_nonneg_left (show
    Ed t / (2 * Real.sqrt (E t + eta)) - C * Real.sqrt (E t + eta) ≤ force t by linarith) hfpos
  exact hmul.trans (by nlinarith [mul_le_mul_of_nonneg_right hfactor hforce])

theorem regularized_sqrt_energy_gronwall
    {E Ed force : ℝ → ℝ} {C a b eta : ℝ} (hab : a ≤ b)
    (hEcont : ContinuousOn E (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt E (Ed t) t)
    (hE : ∀ t ∈ Icc a b, 0 ≤ E t)
    (hforce : ContinuousOn force (Icc a b))
    (hforcepos : ∀ t ∈ Icc a b, 0 ≤ force t)
    (hC : 0 ≤ C) (heta : 0 < eta)
    (hineq : ∀ t ∈ Ioo a b, Ed t ≤ C * E t + Real.sqrt (2 * E t) * force t) :
    Real.sqrt (E b + eta) ≤ Real.exp (C * (b - a)) *
      (Real.sqrt (E a + eta) + ∫ t in a..b, force t) := by
  have hwcont : ContinuousOn (regularizedWeightedEnergy E C a eta) (Icc a b) := by
    exact (show Continuous (fun t : ℝ => Real.exp (-C * (t - a))) by fun_prop).continuousOn.mul
      ((hEcont.add continuousOn_const).sqrt)
  have hwderiv (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivWithinAt (regularizedWeightedEnergy E C a eta)
        (regularizedWeightedRate E Ed C a eta t) (Ioi t) t :=
    (regularizedWeightedEnergy_hasDerivAt (hderiv t ht)
      (hE t ⟨ht.1.le, ht.2.le⟩) heta).hasDerivWithinAt
  have hint := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hwcont hwderiv
    (hforce.integrableOn_compact isCompact_Icc) (fun t ht =>
      regularizedWeightedRate_le (hE t ⟨ht.1.le, ht.2.le⟩)
        (hforcepos t ⟨ht.1.le, ht.2.le⟩) hC heta ht.1.le (hineq t ht))
  have hw : Real.exp (-C * (b - a)) * Real.sqrt (E b + eta) ≤
      Real.sqrt (E a + eta) + ∫ t in a..b, force t := by
    simpa only [regularizedWeightedEnergy, sub_self, mul_zero, Real.exp_zero, one_mul,
      sub_le_iff_le_add, add_comm] using hint
  have hmul := mul_le_mul_of_nonneg_left hw (Real.exp_pos (C * (b - a))).le
  have hexp : Real.exp (C * (b - a)) * Real.exp (-C * (b - a)) = 1 := by
    rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
  simpa only [← mul_assoc, hexp, one_mul] using hmul

theorem sqrt_energy_gronwall
    {E Ed force : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (hEcont : ContinuousOn E (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt E (Ed t) t)
    (hE : ∀ t ∈ Icc a b, 0 ≤ E t)
    (hforce : ContinuousOn force (Icc a b))
    (hforcepos : ∀ t ∈ Icc a b, 0 ≤ force t)
    (hC : 0 ≤ C)
    (hineq : ∀ t ∈ Ioo a b, Ed t ≤ C * E t + Real.sqrt (2 * E t) * force t) :
    Real.sqrt (E b) ≤ Real.exp (C * (b - a)) *
      (Real.sqrt (E a) + ∫ t in a..b, force t) := by
  have ht0 : Tendsto (fun eta : ℝ => eta) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuousWithinAt_id.tendsto
  have hleft : Tendsto (fun eta : ℝ => Real.sqrt (E b + eta))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt (E b))) := by
    simpa only [add_zero] using (tendsto_const_nhds.add ht0).sqrt
  have hright : Tendsto (fun eta : ℝ => Real.exp (C * (b - a)) *
      (Real.sqrt (E a + eta) + ∫ t in a..b, force t)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.exp (C * (b - a)) * (Real.sqrt (E a) + ∫ t in a..b, force t))) := by
    simpa only [add_zero] using tendsto_const_nhds.mul
      (((tendsto_const_nhds.add ht0).sqrt).add tendsto_const_nhds)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with eta heta
  exact regularized_sqrt_energy_gronwall hab hEcont hderiv hE hforce hforcepos hC heta hineq

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

@[simp] theorem stateSegment_zero (w0 w1 : DarbouxState) : stateSegment w0 w1 0 = w0 := by
  simp [stateSegment]

@[simp] theorem stateSegment_one (w0 w1 : DarbouxState) : stateSegment w0 w1 1 = w1 := by
  simp [stateSegment]

theorem stateSegment_hasDerivAt (w0 w1 : DarbouxState) (sigma : ℝ) :
    HasDerivAt (stateSegment w0 w1) (w1 - w0) sigma := by
  have he : (AffineMap.lineMap w0 w1 : ℝ → DarbouxState) = stateSegment w0 w1 := by
    funext t
    ext i
    simp [AffineMap.lineMap_apply_module, stateSegment]
  rw [← he]
  exact AffineMap.hasDerivAt_lineMap

theorem stateSegment_continuous (w0 w1 : DarbouxState) : Continuous (stateSegment w0 w1) :=
  continuous_iff_continuousAt.mpr (fun sigma => (stateSegment_hasDerivAt w0 w1 sigma).continuousAt)

theorem statePoint_qHeightJetSegment (z0 z : Coord → ℝ) (sigma : ℝ) (p : Coord) :
    statePoint (qHeightJetSegment z0 z sigma p) = p := by
  rw [qHeightJetSegment, statePoint_segment (by simp only [statePoint_qSolutionJet]),
    statePoint_qSolutionJet]

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

theorem inward_interval_geometry
    {xl xr a b speed radius t : ℝ} (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hxl : -radius < xl) (hxr : xr < radius)
    (hlength : 2 * speed * (b - a) < xr - xl) (ht : t ∈ Icc a b) :
    inwardLeft xl a speed t ∈ Ioo (-radius) radius ∧
    inwardRight xr a speed t ∈ Ioo (-radius) radius ∧
    inwardLeft xl a speed t < inwardRight xr a speed t ∧
    0 < xr - xl - 2 * speed * (b - a) ∧
    xr - xl - 2 * speed * (b - a) ≤
      inwardRight xr a speed t - inwardLeft xl a speed t := by
  have hinc : 0 ≤ speed * (t - a) := mul_nonneg hspeed (sub_nonneg.mpr ht.1)
  have hmax := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hspeed
  have hspan : 0 ≤ speed * (b - a) := mul_nonneg hspeed (sub_nonneg.mpr hab)
  have hupper : speed * (t - a) < xr - xl := by
    linarith only [hmax, hspan, hlength]
  unfold inwardLeft inwardRight
  constructor
  · constructor
    · linarith
    · linarith only [hupper, hxr]
  constructor
  · constructor <;> linarith
  constructor
  · linarith
  constructor <;> linarith

theorem movingSourceNorm_continuousOn
    {R : Coord → ℝ} {radius lo hi xl xr a b speed : ℝ}
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hleft : ∀ t ∈ Icc a b, inwardLeft xl a speed t ∈ Ioo (-radius) radius)
    (hright : ∀ t ∈ Icc a b, inwardRight xr a speed t ∈ Ioo (-radius) radius)
    (htime : Icc a b ⊆ Ioo lo hi) :
    ContinuousOn (movingSourceNorm xl xr a speed R) (Icc a b) := by
  intro t ht
  have hd := inwardIntervalIntegral_hasDerivAt (hR.pow 2) hradius
    (hleft t ht) (hright t ht) (htime ht)
  exact hd.continuousAt.sqrt.continuousWithinAt

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem stateQDenominator_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateQDenominator g) (stateBaseDomain U) :=
  (contDiffOn_apply ℝ ℝ 5 _).sub (stateConnection_contDiffOn hg hU 0 0)

def qCompactTube (g : MetricField) (S : Set Coord) (M c : ℝ) : Set DarbouxState :=
  stateBaseCompact S M ∩ (fun w => |stateQDenominator g w|) ⁻¹' Ici c

theorem qCompactTube_isCompact {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M c : ℝ) : IsCompact (qCompactTube g S M c) := by
  have hbase := stateBaseCompact_isCompact hS M
  have hc : ContinuousOn (fun w => |stateQDenominator g w|) (stateBaseCompact S M) :=
    (stateQDenominator_contDiffOn hg hU).continuousOn.abs.mono (fun w hw => hSU hw.1)
  have hclosed : IsClosed (qCompactTube g S M c) :=
    hc.preimage_isClosed_of_isClosed hbase.isClosed isClosed_Ici
  exact hbase.of_isClosed_subset hclosed inter_subset_left

theorem qCompactTube_subset_domain {g : MetricField} {U S : Set Coord}
    (hSU : S ⊆ U) (M : ℝ) {c : ℝ} (hc : 0 < c) :
    qCompactTube g S M c ⊆ darbouxQStateDomain g U := by
  intro w hw
  refine ⟨hSU hw.1.1, ?_⟩
  intro hz
  have hh : c ≤ |stateQDenominator g w| := hw.2
  rw [hz, abs_zero] at hh
  linarith

theorem qCompactTube_derivative_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) {f : DarbouxState → ℝ}
    (hf : ContDiffOn ℝ ∞ f (darbouxQStateDomain g U)) (k : ℕ) :
    ∃ C : ℝ, ∀ w ∈ qCompactTube g S M c, ‖iteratedFDeriv ℝ k f w‖ ≤ C := by
  have hDo := darbouxQStateDomain_isOpen hg hU
  have hcont : ContinuousOn (iteratedFDeriv ℝ k f) (darbouxQStateDomain g U) := by
    apply (hf.continuousOn_iteratedFDerivWithin (WithTop.coe_le_coe.mpr le_top)
      hDo.uniqueDiffOn).congr
    intro w hw
    exact (iteratedFDerivWithin_eq_iteratedFDeriv hDo.uniqueDiffOn
      ((hf.contDiffAt (hDo.mem_nhds hw)).of_le (WithTop.coe_le_coe.mpr le_top)) hw).symm
  exact (qCompactTube_isCompact hg hU hS hSU M c).exists_bound_of_continuousOn
    (hcont.mono (qCompactTube_subset_domain hSU M hc))

theorem qCoefficient_uniform_derivative_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) (i : Fin 6) (k : ℕ) :
    ∃ C : ℝ, ∀ w ∈ qCompactTube g S M c,
      ‖iteratedFDeriv ℝ k (qFirstCoefficient g i) w‖ ≤ C :=
  qCompactTube_derivative_bound hg hU hS hSU M hc (qFirstCoefficient_contDiffOn hg hU i) k

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

variable {P S bTheta bXi v R : Coord → ℝ} {radius lo hi xl xr theta0 speed theta : ℝ}

theorem movingEnergy_hasDerivAt_of_sliceEquation
    (hP : ContDiffOn ℝ ∞ P (coordinateRectangle radius lo hi))
    (hS : ContDiffOn ℝ ∞ S (coordinateRectangle radius lo hi))
    (hbt : ContDiffOn ℝ ∞ bTheta (coordinateRectangle radius lo hi))
    (hbx : ContDiffOn ℝ ∞ bXi (coordinateRectangle radius lo hi))
    (hv : ContDiffOn ℝ ∞ v (coordinateRectangle radius lo hi))
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi))
    (hradius : 0 < radius)
    (hl : inwardLeft xl theta0 speed theta ∈ Ioo (-radius) radius)
    (hr : inwardRight xr theta0 speed theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi)
    (hEq : ∀ x ∈ uIcc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta),
      hyperbolicOperator P S v (coordinatePoint x theta) =
        bTheta (coordinatePoint x theta) * coordPartial 1 v (coordinatePoint x theta) +
        bXi (coordinatePoint x theta) * coordPartial 0 v (coordinatePoint x theta) +
        R (coordinatePoint x theta)) :
    HasDerivAt (movingEnergy xl xr theta0 speed S v)
      (movingEnergyRate xl xr theta0 speed P S bTheta bXi v R theta) theta := by
  let U := coordinateRectangle radius lo hi
  have hU : IsOpen U := coordinateRectangle_isOpen radius lo hi
  obtain ⟨he, hj, herr⟩ := energy_fields_contDiffOn hU hP hS hbt hbx hv
  have hrest : ContDiffOn ℝ ∞
      (fun p => energyCoefficientError P S bTheta bXi v p + R p * coordPartial 1 v p) U :=
    herr.add (hR.mul (partial_contDiffOn hv hU 1))
  have hmem {x : ℝ}
      (hx : x ∈ uIcc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta)) :
      coordinatePoint x theta ∈ U :=
    point_mem_rectangle
      ⟨lt_of_lt_of_le (lt_min hl.1 hr.1) hx.1,
        lt_of_le_of_lt hx.2 (max_lt hl.2 hr.2)⟩ htheta
  have hlocal (x : ℝ)
      (hx : x ∈ uIcc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta)) :
      coordPartial 1 (energyDensity S v) (coordinatePoint x theta) =
        coordPartial 0 (energyFlux P S v) (coordinatePoint x theta) +
          (energyCoefficientError P S bTheta bXi v (coordinatePoint x theta) +
            R (coordinatePoint x theta) * coordPartial 1 v (coordinatePoint x theta)) := by
    have hp := hmem hx
    have hh := energy_density_flux_identity
      ((hP.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
      ((hS.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) hv hU hp (hEq x hx)
    linarith
  have hint :
      (∫ x in inwardLeft xl theta0 speed theta..inwardRight xr theta0 speed theta,
        coordPartial 1 (energyDensity S v) (coordinatePoint x theta)) =
      energyFlux P S v (coordinatePoint (inwardRight xr theta0 speed theta) theta) -
        energyFlux P S v (coordinatePoint (inwardLeft xl theta0 speed theta) theta) +
      movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
        (fun p => energyCoefficientError P S bTheta bXi v p + R p * coordPartial 1 v p) theta := by
    calc
      _ = ∫ x in inwardLeft xl theta0 speed theta..inwardRight xr theta0 speed theta,
          coordPartial 0 (energyFlux P S v) (coordinatePoint x theta) +
            (energyCoefficientError P S bTheta bXi v (coordinatePoint x theta) +
              R (coordinatePoint x theta) * coordPartial 1 v (coordinatePoint x theta)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hlocal x hx
      _ = _ := by
        rw [intervalIntegral.integral_add
          (slice_intervalIntegrable (partial_contDiffOn hj hU 0).continuousOn hl hr htheta)
          (slice_intervalIntegrable hrest.continuousOn hl hr htheta),
          slice_integral_partial_xi hj hl hr htheta]
        rfl
  have hd := inwardIntervalIntegral_hasDerivAt he hradius hl hr htheta
  rw [hint] at hd
  convert hd using 1 <;> try with_reducible_and_instances rfl
  · rfl
  · dsimp only [movingEnergyRate]
    ring

theorem moving_source_integral_bound_of_slicePositivity
    (hS : ContDiffOn ℝ ∞ S (coordinateRectangle radius lo hi))
    (hv : ContDiffOn ℝ ∞ v (coordinateRectangle radius lo hi))
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi))
    (hl : inwardLeft xl theta0 speed theta ∈ Ioo (-radius) radius)
    (hr : inwardRight xr theta0 speed theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi)
    (hlr : inwardLeft xl theta0 speed theta ≤ inwardRight xr theta0 speed theta)
    (hSpos : ∀ x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta),
      0 ≤ S (coordinatePoint x theta)) :
    movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
      (fun p => R p * coordPartial 1 v p) theta ≤
      Real.sqrt (2 * movingEnergy xl xr theta0 speed S v theta) *
        movingSourceNorm xl xr theta0 speed R theta := by
  let l := inwardLeft xl theta0 speed theta
  let r := inwardRight xr theta0 speed theta
  let U := coordinateRectangle radius lo hi
  have hU : IsOpen U := coordinateRectangle_isOpen radius lo hi
  have hmem {x : ℝ} (hx : x ∈ Icc l r) : coordinatePoint x theta ∈ U :=
    point_mem_rectangle ⟨hl.1.trans_le hx.1, hx.2.trans_lt hr.2⟩ htheta
  have hvt := partial_contDiffOn hv hU 1
  have hx := partial_contDiffOn hv hU 0
  have he : ContDiffOn ℝ ∞ (energyDensity S v) U :=
    ((hvt.pow 2).add (hS.mul (hx.pow 2))).div_const 2
  have he2 : ContDiffOn ℝ ∞ (fun p => 2 * energyDensity S v p) U :=
    contDiffOn_const.mul he
  have hcR : ContinuousOn (fun x => R (coordinatePoint x theta)) (Icc l r) :=
    hR.continuousOn.comp (by unfold coordinatePoint; fun_prop) (fun x hx => hmem hx)
  have hcvt : ContinuousOn (fun x => coordPartial 1 v (coordinatePoint x theta)) (Icc l r) :=
    hvt.continuousOn.comp (by unfold coordinatePoint; fun_prop) (fun x hx => hmem hx)
  have hC := interval_product_abs_le_sqrt_squares hlr hcR hcvt
  have hkin : (∫ x in l..r, (coordPartial 1 v (coordinatePoint x theta)) ^ 2) ≤
      2 * movingEnergy xl xr theta0 speed S v theta := by
    have hI := intervalIntegral.integral_mono_on hlr
      (slice_intervalIntegrable (hvt.pow 2).continuousOn hl hr htheta)
      (slice_intervalIntegrable he2.continuousOn hl hr htheta)
      (fun x hx => by
        have hs := hSpos x hx
        unfold energyDensity
        nlinarith [mul_nonneg hs (sq_nonneg (coordPartial 0 v (coordinatePoint x theta)))])
    simpa only [movingEnergy, movingIntervalIntegral, intervalIntegral.integral_const_mul] using hI
  have hroot := Real.sqrt_le_sqrt hkin
  have hmul := mul_le_mul_of_nonneg_left hroot
    (Real.sqrt_nonneg (∫ x in l..r, R (coordinatePoint x theta) ^ 2))
  unfold movingIntervalIntegral movingSourceNorm
  exact (le_abs_self _).trans (hC.trans
    (by simpa only [l, r, movingIntervalIntegral, mul_comm] using hmul))

theorem movingEnergyRate_le_of_sliceBounds
    (hP : ContDiffOn ℝ ∞ P (coordinateRectangle radius lo hi))
    (hS : ContDiffOn ℝ ∞ S (coordinateRectangle radius lo hi))
    (hbt : ContDiffOn ℝ ∞ bTheta (coordinateRectangle radius lo hi))
    (hbx : ContDiffOn ℝ ∞ bXi (coordinateRectangle radius lo hi))
    (hv : ContDiffOn ℝ ∞ v (coordinateRectangle radius lo hi))
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi))
    (hl : inwardLeft xl theta0 speed theta ∈ Ioo (-radius) radius)
    (hr : inwardRight xr theta0 speed theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi)
    (hlr : inwardLeft xl theta0 speed theta ≤ inwardRight xr theta0 speed theta)
    {s0 M : ℝ} (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hSfloor : ∀ x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta),
      s0 ≤ S (coordinatePoint x theta))
    (hcoeff : ∀ x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta),
      |bTheta (coordinatePoint x theta)| ≤ M ∧ |bXi (coordinatePoint x theta)| ≤ M ∧
      |coordPartial 0 P (coordinatePoint x theta)| ≤ M ∧
      |coordPartial 0 S (coordinatePoint x theta)| ≤ M ∧
      |coordPartial 1 S (coordinatePoint x theta)| ≤ M)
    (hspeed : ∀ x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta),
      |P (coordinatePoint x theta)| + Real.sqrt (S (coordinatePoint x theta)) ≤ speed) :
    movingEnergyRate xl xr theta0 speed P S bTheta bXi v R theta ≤
      (8 * M * (1 + 1 / s0)) * movingEnergy xl xr theta0 speed S v theta +
      Real.sqrt (2 * movingEnergy xl xr theta0 speed S v theta) *
        movingSourceNorm xl xr theta0 speed R theta := by
  let U := coordinateRectangle radius lo hi
  have hU : IsOpen U := coordinateRectangle_isOpen radius lo hi
  obtain ⟨he, hj, herr⟩ := energy_fields_contDiffOn hU hP hS hbt hbx hv
  have heC : ContDiffOn ℝ ∞
      (fun p => (8 * M * (1 + 1 / s0)) * energyDensity S v p) U :=
    contDiffOn_const.mul he
  have hsource := hR.mul (partial_contDiffOn hv hU 1)
  have hmem {x : ℝ}
      (hx : x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta)) :
      coordinatePoint x theta ∈ U :=
    point_mem_rectangle ⟨hl.1.trans_le hx.1, hx.2.trans_lt hr.2⟩ htheta
  have hSl := hSfloor _ ⟨le_rfl, hlr⟩
  have hSr := hSfloor _ ⟨hlr, le_rfl⟩
  have hboundary := inward_boundary_nonpositive (v := v) (hs0.le.trans hSl) (hs0.le.trans hSr)
    (hspeed _ ⟨le_rfl, hlr⟩) (hspeed _ ⟨hlr, le_rfl⟩)
  have herrI : movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
      (energyCoefficientError P S bTheta bXi v) theta ≤
      (8 * M * (1 + 1 / s0)) * movingEnergy xl xr theta0 speed S v theta := by
    have hh := intervalIntegral.integral_mono_on hlr
      (slice_intervalIntegrable herr.continuousOn hl hr htheta)
      (slice_intervalIntegrable heC.continuousOn hl hr htheta)
      (fun x hx => by
        obtain ⟨hbt', hbx', hPx', hSx', hSt'⟩ := hcoeff x hx
        exact (le_abs_self _).trans (energyCoefficientError_abs_le hs0
          (hSfloor x hx) hM hbt' hbx' hPx' hSx' hSt'))
    simpa only [movingIntervalIntegral, movingEnergy, intervalIntegral.integral_const_mul] using hh
  have hsourceI := moving_source_integral_bound_of_slicePositivity hS hv hR hl hr htheta hlr
    (fun p hp => hs0.le.trans (hSfloor p hp))
  unfold movingEnergyRate movingIntervalIntegral
  rw [intervalIntegral.integral_add
    (slice_intervalIntegrable herr.continuousOn hl hr htheta)
    (slice_intervalIntegrable hsource.continuousOn hl hr htheta)]
  dsimp only [movingIntervalIntegral] at herrI hsourceI
  linarith

theorem point_mem_shrinkingSlab {xl xr a b speed x t : ℝ}
    (ht : t ∈ Icc a b)
    (hx : x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t)) :
    coordinatePoint x t ∈ shrinkingSlab xl xr a b speed := by
  simpa [shrinkingSlab, coordinatePoint] using And.intro ht hx

theorem moving_slab_energy_propagation
    {P S bTheta bXi v R : Coord → ℝ} {radius lo hi xl xr a b speed s0 M : ℝ}
    (hP : ContDiffOn ℝ ∞ P (coordinateRectangle radius lo hi))
    (hS : ContDiffOn ℝ ∞ S (coordinateRectangle radius lo hi))
    (hbt : ContDiffOn ℝ ∞ bTheta (coordinateRectangle radius lo hi))
    (hbx : ContDiffOn ℝ ∞ bXi (coordinateRectangle radius lo hi))
    (hv : ContDiffOn ℝ ∞ v (coordinateRectangle radius lo hi))
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi))
    (hradius : 0 < radius) (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hxl : -radius < xl) (hxr : xr < radius)
    (ha : a ∈ Ioo lo hi) (hb : b ∈ Ioo lo hi)
    (hlength : 2 * speed * (b - a) < xr - xl)
    (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hSfloor : ∀ p ∈ shrinkingSlab xl xr a b speed, s0 ≤ S p)
    (hcoeff : ∀ p ∈ shrinkingSlab xl xr a b speed,
      |bTheta p| ≤ M ∧ |bXi p| ≤ M ∧ |coordPartial 0 P p| ≤ M ∧
        |coordPartial 0 S p| ≤ M ∧ |coordPartial 1 S p| ≤ M)
    (hchar : ∀ p ∈ shrinkingSlab xl xr a b speed, |P p| + Real.sqrt (S p) ≤ speed)
    (hEq : ∀ p ∈ shrinkingSlab xl xr a b speed, hyperbolicOperator P S v p =
      bTheta p * coordPartial 1 v p + bXi p * coordPartial 0 v p + R p) :
    Real.sqrt (movingEnergy xl xr a speed S v b) ≤
      Real.exp ((8 * M * (1 + 1 / s0)) * (b - a)) *
        (Real.sqrt (∫ xi in xl..xr, energyDensity S v (coordinatePoint xi a)) +
          ∫ t in a..b, movingSourceNorm xl xr a speed R t) := by
  have htime : Icc a b ⊆ Ioo lo hi :=
    fun t ht => ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
  have hgeo (t : ℝ) (ht : t ∈ Icc a b) :=
    inward_interval_geometry hab hspeed hxl hxr hlength ht
  have hleft (t : ℝ) (ht : t ∈ Icc a b) := (hgeo t ht).1
  have hright (t : ℝ) (ht : t ∈ Icc a b) := (hgeo t ht).2.1
  have horder (t : ℝ) (ht : t ∈ Icc a b) := (hgeo t ht).2.2.1.le
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (movingEnergy xl xr a speed S v)
        (movingEnergyRate xl xr a speed P S bTheta bXi v R t) t := by
    apply movingEnergy_hasDerivAt_of_sliceEquation hP hS hbt hbx hv hR hradius
      (hleft t ht) (hright t ht) (htime ht)
    intro x hx
    rw [uIcc_of_le (horder t ht)] at hx
    exact hEq _ (point_mem_shrinkingSlab ht hx)
  have hEcont : ContinuousOn (movingEnergy xl xr a speed S v) (Icc a b) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hEpos (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ movingEnergy xl xr a speed S v t := by
    apply movingEnergy_nonneg (horder t ht)
    intro x hx
    exact hs0.le.trans (hSfloor _ (point_mem_shrinkingSlab ht hx))
  have hforce := movingSourceNorm_continuousOn hR hradius hleft hright htime
  have hC : 0 ≤ 8 * M * (1 + 1 / s0) := by positivity
  have hbound (t : ℝ) (ht : t ∈ Ioo a b) :
      movingEnergyRate xl xr a speed P S bTheta bXi v R t ≤
        (8 * M * (1 + 1 / s0)) * movingEnergy xl xr a speed S v t +
          Real.sqrt (2 * movingEnergy xl xr a speed S v t) * movingSourceNorm xl xr a speed R t := by
    apply movingEnergyRate_le_of_sliceBounds hP hS hbt hbx hv hR
      (hleft t ⟨ht.1.le, ht.2.le⟩) (hright t ⟨ht.1.le, ht.2.le⟩)
      (htime ⟨ht.1.le, ht.2.le⟩) (horder t ⟨ht.1.le, ht.2.le⟩) hs0 hM
    · intro x hx
      exact hSfloor _ (point_mem_shrinkingSlab ⟨ht.1.le, ht.2.le⟩ hx)
    · intro x hx
      exact hcoeff _ (point_mem_shrinkingSlab ⟨ht.1.le, ht.2.le⟩ hx)
    · intro x hx
      exact hchar _ (point_mem_shrinkingSlab ⟨ht.1.le, ht.2.le⟩ hx)
  have hfinal := sqrt_energy_gronwall hab hEcont
    (fun t ht => hderiv t ⟨ht.1.le, ht.2.le⟩) hEpos hforce
    (fun t _ => Real.sqrt_nonneg _) hC hbound
  simpa only [movingEnergy, movingIntervalIntegral, inwardLeft, inwardRight,
    sub_self, mul_zero, add_zero, sub_zero] using hfinal

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem sixVariableQ_fderiv_apply (g : MetricField) (w v : DarbouxState) :
    fderiv ℝ (sixVariableQ g) w v = ∑ i, qFirstCoefficient g i w * v i := by
  calc
    _ = fderiv ℝ (sixVariableQ g) w (∑ i, v i • Pi.single i 1) :=
      congrArg (fderiv ℝ (sixVariableQ g) w) (pi_eq_sum_univ' v)
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, qFirstCoefficient, mul_comm]

theorem qCoefficient_segment_continuousOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U) (i : Fin 6) :
    ContinuousOn (fun sigma => qFirstCoefficient g i (stateSegment w0 w1 sigma)) (Icc (0 : ℝ) 1) :=
  (qFirstCoefficient_contDiffOn hg hU i).continuousOn.comp
    (stateSegment_continuous w0 w1).continuousOn (fun t ht => hsegment t ht)

theorem sixVariableQ_segment_FTC {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U) :
    sixVariableQ g w1 - sixVariableQ g w0 =
      ∑ i, averagedQCoefficient g w0 w1 i * (w1 i - w0 i) := by
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun sigma => sixVariableQ g (stateSegment w0 w1 sigma))
        (∑ i, qFirstCoefficient g i (stateSegment w0 w1 t) * (w1 i - w0 i)) t := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have hQ := ((sixVariableQ_contDiffOn hg hU).contDiffAt
      ((darbouxQStateDomain_isOpen hg hU).mem_nhds (hsegment t ht'))).differentiableAt (by simp)
    have hh := hQ.hasFDerivAt.comp_hasDerivAt t (stateSegment_hasDerivAt w0 w1 t)
    change HasDerivAt (fun sigma => sixVariableQ g (stateSegment w0 w1 sigma))
      (fderiv ℝ (sixVariableQ g) (stateSegment w0 w1 t) (w1 - w0)) t at hh
    rw [sixVariableQ_fderiv_apply] at hh
    exact hh
  have hi (i : Fin 6) : IntervalIntegrable
      (fun sigma => qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i))
        volume (0 : ℝ) 1 :=
    ((qCoefficient_segment_continuousOn hg hU hsegment i).mul_const _).intervalIntegrable_of_Icc zero_le_one
  have hint : IntervalIntegrable
      (fun sigma => ∑ i, qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i))
        volume (0 : ℝ) 1 := by
    have hh := IntervalIntegrable.sum Finset.univ (fun i _ => hi i)
    change IntervalIntegrable
      (fun sigma => ∑ i, qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i))
      volume (0 : ℝ) 1 at hh
    exact hh
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [stateSegment_zero, stateSegment_one] at hFTC
  calc
    _ = ∫ sigma in (0 : ℝ)..1, ∑ i,
        qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i) := hFTC.symm
    _ = ∑ i, ∫ sigma in (0 : ℝ)..1,
        qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i) :=
      intervalIntegral.integral_finsetSum (fun i _ => hi i)
    _ = _ := by simp only [intervalIntegral.integral_mul_const, averagedQCoefficient]

theorem averagedQCoefficient_lower {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U)
    (i : Fin 6) {gamma : ℝ}
    (hgamma : ∀ sigma ∈ Icc (0 : ℝ) 1, gamma ≤ qFirstCoefficient g i (stateSegment w0 w1 sigma)) :
    gamma ≤ averagedQCoefficient g w0 w1 i := by
  have hi : IntervalIntegrable
      (fun sigma => qFirstCoefficient g i (stateSegment w0 w1 sigma)) volume (0 : ℝ) 1 :=
    (qCoefficient_segment_continuousOn hg hU hsegment i).intervalIntegrable_of_Icc zero_le_one
  have hc : IntervalIntegrable (fun _ : ℝ => gamma) volume (0 : ℝ) 1 := intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on zero_le_one hc hi hgamma
  simpa [averagedQCoefficient] using h

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem qSolutionJet_contDiffOn {z : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (qSolutionJet z) U := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_apply ℝ ℝ 0 U
  · exact contDiffOn_apply ℝ ℝ 1 U
  · exact partial_contDiffOn hz hU 0
  · exact partial_contDiffOn hz hU 1
  · exact partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0
  · exact partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem real_near_closed_interval {a b e x : ℝ} (hab : a ≤ b)
    (he : 0 < e) (hx : x ∈ Ioo (a-e) (b+e)) :
    ∃ y ∈ Icc a b, |x-y| < e := by
  by_cases hxa : x < a
  · refine ⟨a,⟨le_rfl,hab⟩,?_⟩
    rw [abs_of_neg (sub_neg.mpr hxa)]
    linarith [hx.1]
  by_cases hbx : b < x
  · refine ⟨b,⟨hab,le_rfl⟩,?_⟩
    rw [abs_of_pos (sub_pos.mpr hbx)]
    linarith [hx.2]
  exact ⟨x,⟨le_of_not_gt hxa,le_of_not_gt hbx⟩,by simpa using he⟩

theorem closedRectangle_compact (l r a b : ℝ) : IsCompact (closedRectangle l r a b) := by
  have he : closedRectangle l r a b = Icc (![l,a] : Coord) ![r,b] := by
    ext p
    constructor
    · intro hp
      constructor
      · intro i
        fin_cases i
        · exact hp.1.1
        · exact hp.2.1
      · intro i
        fin_cases i
        · exact hp.1.2
        · exact hp.2.2
    · intro hp
      exact ⟨⟨hp.1 0,hp.2 0⟩,⟨hp.1 1,hp.2 1⟩⟩
  rw [he]
  exact isCompact_Icc

theorem exists_containing_coordinateRectangle {U : Set Coord} (hU : IsOpen U)
    {R a b : ℝ} (hR : 0 < R) (hab : a ≤ b)
    (hbox : closedRectangle (-R) R a b ⊆ U) :
    ∃ radius lo hi : ℝ, R < radius ∧ lo < a ∧ b < hi ∧
      coordinateRectangle radius lo hi ⊆ U := by
  obtain ⟨e,he,hthick⟩ := (closedRectangle_compact (-R) R a b).exists_thickening_subset_open hU hbox
  refine ⟨R+e,a-e,b+e,by linarith,by linarith,by linarith,?_⟩
  intro p hp
  obtain ⟨x,hx,hxe⟩ := real_near_closed_interval (show -R ≤ R by linarith) he
    (show p 0 ∈ Ioo (-R-e) (R+e) by
      exact ⟨by linarith [hp.1.1],hp.1.2⟩)
  obtain ⟨t,ht,hte⟩ := real_near_closed_interval hab he hp.2
  apply hthick
  rw [Metric.mem_thickening_iff]
  refine ⟨![x,t],⟨hx,ht⟩,?_⟩
  rw [dist_eq_norm]
  apply (pi_norm_lt_iff he).mpr
  intro i
  fin_cases i
  · change ‖p 0-x‖ < e
    simpa only [Real.norm_eq_abs] using hxe
  · change ‖p 1-t‖ < e
    simpa only [Real.norm_eq_abs] using hte

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem qSolutionJet_norm_bound_of_words {z : Coord → ℝ} {p : Coord} {R Z : ℝ}
    (hR : 0 ≤ R) (hpB : ‖p‖ ≤ R)
    (hjet : ∀ ds : List (Fin 2), ds.length ≤ 2 → |iteratedCoordPartial ds z p| ≤ Z) :
    ‖qSolutionJet z p‖ ≤ max R Z := by
  have hcoord (i : Fin 2) : |p i| ≤ R := (norm_le_pi_norm p i).trans hpB
  apply (pi_norm_le_iff_of_nonneg (hR.trans (le_max_left _ _))).mpr
  intro i
  fin_cases i
  · exact (hcoord 0).trans (le_max_left _ _)
  · exact (hcoord 1).trans (le_max_left _ _)
  · exact (hjet [0] (by norm_num)).trans (le_max_right _ _)
  · exact (hjet [1] (by norm_num)).trans (le_max_right _ _)
  · exact (hjet [0, 1] (by norm_num)).trans (le_max_right _ _)
  · exact (hjet [0, 0] (by norm_num)).trans (le_max_right _ _)

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Taylor
open SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem actual_comparison_mean_identity
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (P z : Coord → ℝ) (p : Coord)
    (hseg : ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) :
    sixVariableQ g (qSolutionJet z p)-sixVariableQ g (qSolutionJet P p) =
      comparisonCoefficient g P z 2 p*(coordPartial 0 z p-coordPartial 0 P p)+
      comparisonCoefficient g P z 3 p*(coordPartial 1 z p-coordPartial 1 P p)+
      comparisonCoefficient g P z 4 p*(coordPartial 0 (coordPartial 1 z) p-
        coordPartial 0 (coordPartial 1 P) p)+
      comparisonCoefficient g P z 5 p*(coordPartial 0 (coordPartial 0 z) p-
        coordPartial 0 (coordPartial 0 P) p) := by
  have hh := sixVariableQ_segment_FTC hg hU hseg
  convert hh using 1 <;> try with_reducible_and_instances rfl
  simp [comparisonCoefficient,Fin.sum_univ_succ,qSolutionJet]
  ring

theorem comparison_equation_from_darboux
    {g g0 : MetricField} {U : Set Coord} {P z : Coord → ℝ}
    (hg : SmoothPositiveOn g U) (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U) {p : Coord} (hp : p ∈ U)
    (hD : (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p)
    (hxx : covHessian g z p 0 0 ≠ 0)
    (hseg : ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g0 U) :
    hyperbolicOperator (comparisonCoefficient g0 P z 4) (comparisonCoefficient g0 P z 5)
      (comparisonDifference P z) p =
        comparisonCoefficient g0 P z 3 p*coordPartial 1 (comparisonDifference P z) p+
        comparisonCoefficient g0 P z 2 p*coordPartial 0 (comparisonDifference P z) p+
        (sixVariableQ g (qSolutionJet z p)-sixVariableQ g0 (qSolutionJet z p)-qResidual g0 P p) := by
  have hQ := (darbouxDet_iff_sixVariableQ hg hU hz hp hxx).mp hD
  have hmean := actual_comparison_mean_identity hg0 hU P z p hseg
  have hsub (ds : List (Fin 2)) := CoordinateBound.iterated_sub hz hP hU ds hp
  have h0 : coordPartial 0 (comparisonDifference P z) p = coordPartial 0 z p-coordPartial 0 P p := hsub [0]
  have h1 : coordPartial 1 (comparisonDifference P z) p = coordPartial 1 z p-coordPartial 1 P p := hsub [1]
  have h00 : coordPartial 0 (coordPartial 0 (comparisonDifference P z)) p =
      coordPartial 0 (coordPartial 0 z) p-coordPartial 0 (coordPartial 0 P) p := hsub [0,0]
  have h01 : coordPartial 0 (coordPartial 1 (comparisonDifference P z)) p =
      coordPartial 0 (coordPartial 1 z) p-coordPartial 0 (coordPartial 1 P) p := hsub [0,1]
  have h11 : coordPartial 1 (coordPartial 1 (comparisonDifference P z)) p =
      coordPartial 1 (coordPartial 1 z) p-coordPartial 1 (coordPartial 1 P) p := hsub [1,1]
  unfold hyperbolicOperator qResidual
  rw [h0,h1,h00,h01,h11,hQ]
  linarith

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem coordPartial_qSolutionJet_norm_bound
    {z : Coord → ℝ} {U S : Set Coord} {Z : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hSU : S ⊆ U)
    (hzB : CoordinateBound z S 3 Z) {p : Coord} (hp : p ∈ S) (j : Fin 2) :
    ‖coordPartial j (qSolutionJet z) p‖ ≤ max 1 Z := by
  have hJ : DifferentiableAt ℝ (qSolutionJet z) p :=
    ((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds (hSU hp))).differentiableAt (by simp)
  have he (i : Fin 6) : coordPartial j (qSolutionJet z) p i =
      coordPartial j (fun r => qSolutionJet z r i) p := by
    unfold coordPartial
    rw [fderiv_apply hJ i]
    rfl
  apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans (le_max_left _ _))).mpr
  intro i
  rw [he, Real.norm_eq_abs]
  fin_cases i
  · change |coordPartial j (fun r : Coord => r 0) p| ≤ max 1 Z
    rw [DarbouxJetCalculus.coordPartial_eval]
    split_ifs <;> simp only [abs_one, abs_zero]
    · exact le_max_left _ _
    · exact zero_le_one.trans (le_max_left _ _)
  · change |coordPartial j (fun r : Coord => r 1) p| ≤ max 1 Z
    rw [DarbouxJetCalculus.coordPartial_eval]
    split_ifs <;> simp only [abs_one, abs_zero]
    · exact le_max_left _ _
    · exact zero_le_one.trans (le_max_left _ _)
  · change |iteratedCoordPartial [j, 0] z p| ≤ max 1 Z
    exact (hzB [j, 0] (by norm_num) p hp).trans (le_max_right _ _)
  · change |iteratedCoordPartial [j, 1] z p| ≤ max 1 Z
    exact (hzB [j, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · change |iteratedCoordPartial [j, 0, 1] z p| ≤ max 1 Z
    exact (hzB [j, 0, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · change |iteratedCoordPartial [j, 0, 0] z p| ≤ max 1 Z
    exact (hzB [j, 0, 0] (by norm_num) p hp).trans (le_max_right _ _)

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def comparisonStateMap (P z : Coord → ℝ) (q : Coord × ℝ) : DarbouxState :=
  qHeightJetSegment P z q.2 q.1

def comparisonIntegrand (g : MetricField) (P z : Coord → ℝ) (i : Fin 6)
    (q : Coord × ℝ) : ℝ := qFirstCoefficient g i (comparisonStateMap P z q)

def comparisonParameterDomain (g : MetricField) (P z : Coord → ℝ) (U : Set Coord) :
    Set (Coord × ℝ) :=
  (U ×ˢ (univ : Set ℝ)) ∩ comparisonStateMap P z ⁻¹' darbouxQStateDomain g U

theorem comparisonStateMap_contDiffOn {P z : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (comparisonStateMap P z) (U ×ˢ (univ : Set ℝ)) := by
  have h0 : ContDiffOn ℝ ∞ (fun q : Coord × ℝ => qSolutionJet P q.1)
      (U ×ˢ (univ : Set ℝ)) := (qSolutionJet_contDiffOn hU hP).comp contDiff_fst.contDiffOn
    (fun _ hq => hq.1)
  have h1 : ContDiffOn ℝ ∞ (fun q : Coord × ℝ => qSolutionJet z q.1)
      (U ×ˢ (univ : Set ℝ)) := (qSolutionJet_contDiffOn hU hz).comp contDiff_fst.contDiffOn
    (fun _ hq => hq.1)
  exact ((contDiffOn_const.sub contDiff_snd.contDiffOn).smul h0).add
    (contDiff_snd.contDiffOn.smul h1)

theorem comparisonParameterDomain_isOpen {g : MetricField} {P z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U) :
    IsOpen (comparisonParameterDomain g P z U) :=
  (comparisonStateMap_contDiffOn hU hP hz).continuousOn.isOpen_inter_preimage
    (hU.prod isOpen_univ) (darbouxQStateDomain_isOpen hg hU)

theorem comparisonIntegrand_contDiffOn {g : MetricField} {P z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U) (i : Fin 6) :
    ContDiffOn ℝ ∞ (comparisonIntegrand g P z i) (comparisonParameterDomain g P z U) :=
  (qFirstCoefficient_contDiffOn hg hU i).comp
    ((comparisonStateMap_contDiffOn hU hP hz).mono inter_subset_left) (fun _ hq => hq.2)

theorem comparisonCoefficient_eq_parameterIntegral (g : MetricField) (P z : Coord → ℝ)
    (i : Fin 6) :
    comparisonCoefficient g P z i = compactParameterIntegral (comparisonIntegrand g P z i) := by
  funext p
  change (∫ sigma in (0 : ℝ)..1, _) = ∫ sigma in Icc (0 : ℝ) 1, _
  simp only [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  rfl

theorem comparisonCoefficient_contDiffOn {g : MetricField} {P z : Coord → ℝ}
    {U W : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hW : IsOpen W) (hWU : W ⊆ U)
    (hsegment : ∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) (i : Fin 6) :
    ContDiffOn ℝ ∞ (comparisonCoefficient g P z i) W := by
  rw [comparisonCoefficient_eq_parameterIntegral]
  apply compactParameterIntegral_contDiffOn (comparisonIntegrand_contDiffOn hg hU hP hz i)
    (comparisonParameterDomain_isOpen hg hU hP hz) hW
  intro q hq
  exact ⟨⟨hWU hq.1,mem_univ _⟩,hsegment q.1 hq.1 q.2 hq.2⟩

theorem exists_comparison_coefficient_neighborhood
    {g : MetricField} {P z : Coord → ℝ} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hS : IsCompact S) (hSU : S ⊆ U)
    (hsegment : ∀ p ∈ S, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) :
    ∃ W : Set Coord, IsOpen W ∧ S ⊆ W ∧ W ⊆ U ∧
      (∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
        qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) ∧
      ∀ i : Fin 6, ContDiffOn ℝ ∞ (comparisonCoefficient g P z i) W := by
  have hprod : S ×ˢ Icc (0 : ℝ) 1 ⊆ comparisonParameterDomain g P z U := by
    intro q hq
    exact ⟨⟨hSU hq.1,mem_univ _⟩,hsegment q.1 hq.1 q.2 hq.2⟩
  obtain ⟨W,J,hW,_,hSW,hIJ,hWJ⟩ := generalized_tube_lemma hS isCompact_Icc
    (comparisonParameterDomain_isOpen hg hU hP hz) hprod
  have hWU : W ⊆ U := by
    intro p hp
    have hj : (0 : ℝ) ∈ J := hIJ (by norm_num)
    exact (hWJ (show (p, (0 : ℝ)) ∈ W ×ˢ J from ⟨hp,hj⟩)).1.1
  have hseg : ∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U := by
    intro p hp sigma hs
    exact (hWJ (show (p, sigma) ∈ W ×ˢ J from ⟨hp,hIJ hs⟩)).2
  exact ⟨W,hW,hSW,hWU,hseg,fun i => comparisonCoefficient_contDiffOn hg hU hP hz hW hWU hseg i⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Analytic
open SmoothLocal.Geometry

theorem compactParameterIntegral_coordPartial
    {H : Coord × ℝ → ℝ} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContDiffOn ℝ ∞ H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) {p : Coord} (hp : p ∈ U) (j : Fin 2) :
    coordPartial j (compactParameterIntegral H) p =
      ∫ sigma in Icc (0 : ℝ) 1, compactParameterPartial H (p,sigma) (Pi.single j 1) := by
  have hH1 : ContDiffOn ℝ 1 H D := hH.of_le (by simp)
  have hd := compactParameterIntegral_hasFDerivAt hH1 hD hU hUD hp
  have hpart : ContinuousOn (compactParameterPartial H) D :=
    (compactParameterPartial_contDiffOn hD 0 hH1).continuousOn
  have hint : Integrable (fun sigma => compactParameterPartial H (p,sigma))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (parameter_slice_continuousOn hpart hUD hp).integrableOn_compact isCompact_Icc
  change fderiv ℝ (compactParameterIntegral H) p (Pi.single j 1) = _
  rw [hd.fderiv]
  exact ContinuousLinearMap.integral_apply hint (Pi.single j 1)

end SmoothLocal.Analytic

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem comparisonIntegrand_parameter_partial
    {g : MetricField} {P z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} {sigma : ℝ} (hp : p ∈ U)
    (hsegment : qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U)
    (i : Fin 6) (j : Fin 2) :
    compactParameterPartial (comparisonIntegrand g P z i) (p,sigma) (Pi.single j 1) =
      fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)
        ((1-sigma) • coordPartial j (qSolutionJet P) p +
          sigma • coordPartial j (qSolutionJet z) p) := by
  have hJP := ((qSolutionJet_contDiffOn hU hP).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hJz := ((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hQ := ((qFirstCoefficient_contDiffOn hg hU i).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds hsegment)).differentiableAt (by simp)
  have hstate : HasFDerivAt (fun x => qHeightJetSegment P z sigma x)
      ((1-sigma) • fderiv ℝ (qSolutionJet P) p + sigma • fderiv ℝ (qSolutionJet z) p) p :=
    (hJP.hasFDerivAt.const_smul (1-sigma)).add (hJz.hasFDerivAt.const_smul sigma)
  have hchain := hQ.hasFDerivAt.comp p hstate
  have hparam := compactParameter_slice_hasFDerivAt
    ((comparisonIntegrand_contDiffOn hg hU hP hz i).of_le (by simp))
    (comparisonParameterDomain_isOpen hg hU hP hz)
    (show (p,sigma) ∈ comparisonParameterDomain g P z U from
      ⟨⟨hp,mem_univ _⟩,hsegment⟩)
  have he := hparam.unique hchain
  simpa only [ContinuousLinearMap.comp_apply,add_apply,
    smul_apply,coordPartial] using
      congrArg (fun A : Coord →L[ℝ] ℝ => A (Pi.single j 1)) he

theorem comparisonCoefficient_partial
    {g : MetricField} {P z : Coord → ℝ} {U W : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hW : IsOpen W) (hWU : W ⊆ U)
    (hsegment : ∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U)
    {p : Coord} (hp : p ∈ W) (i : Fin 6) (j : Fin 2) :
    coordPartial j (comparisonCoefficient g P z i) p =
      ∫ sigma in (0 : ℝ)..1,
        fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)
          ((1-sigma) • coordPartial j (qSolutionJet P) p +
            sigma • coordPartial j (qSolutionJet z) p) := by
  rw [comparisonCoefficient_eq_parameterIntegral]
  have hUD : W ×ˢ Icc (0 : ℝ) 1 ⊆ comparisonParameterDomain g P z U := by
    intro q hq
    exact ⟨⟨hWU hq.1,mem_univ _⟩,hsegment q.1 hq.1 q.2 hq.2⟩
  rw [compactParameterIntegral_coordPartial (comparisonIntegrand_contDiffOn hg hU hP hz i)
    (comparisonParameterDomain_isOpen hg hU hP hz) hW hUD hp j,
    intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro sigma hs
  exact comparisonIntegrand_parameter_partial hg hU hP hz (hWU hp) (hsegment p hp sigma hs) i j

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem comparison_segment_direction_bound
    {P z : Coord → ℝ} {U T : Set Coord} {Z0 Z sigma : ℝ}
    (hU : IsOpen U) (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hTU : T ⊆ U) (hPZ : CoordinateBound P T 3 Z0) (hzZ : CoordinateBound z T 3 Z)
    {p : Coord} (hp : p ∈ T) (hs : sigma ∈ Icc (0 : ℝ) 1) (j : Fin 2) :
    ‖(1-sigma) • coordPartial j (qSolutionJet P) p +
      sigma • coordPartial j (qSolutionJet z) p‖ ≤ max 1 Z0 + max 1 Z := by
  have h0 := coordPartial_qSolutionJet_norm_bound hU hP hTU hPZ hp j
  have h1 := coordPartial_qSolutionJet_norm_bound hU hz hTU hzZ hp j
  calc
    _ ≤ ‖(1-sigma) • coordPartial j (qSolutionJet P) p‖ +
        ‖sigma • coordPartial j (qSolutionJet z) p‖ := norm_add_le _ _
    _ = (1-sigma)*‖coordPartial j (qSolutionJet P) p‖ +
        sigma*‖coordPartial j (qSolutionJet z) p‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hs.2),abs_of_nonneg hs.1]
    _ ≤ (1-sigma)*max 1 Z0 + sigma*max 1 Z :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hs.2))
        (mul_le_mul_of_nonneg_left h1 hs.1)
    _ ≤ max 1 Z0 + max 1 Z := by
      have hn0 : 0 ≤ max 1 Z0 := zero_le_one.trans (le_max_left _ _)
      have hn1 : 0 ≤ max 1 Z := zero_le_one.trans (le_max_left _ _)
      exact add_le_add (mul_le_of_le_one_left hn0 (by linarith [hs.1]))
        (mul_le_of_le_one_left hn1 hs.2)

theorem exists_uniform_comparison_coefficient_bounds
    {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (R Z0 Z : ℝ) (hR : 0 ≤ R) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P z : Coord → ℝ) (V T : Set Coord),
      IsOpen V → V ⊆ U → ContDiffOn ℝ ∞ P V → ContDiffOn ℝ ∞ z V → T ⊆ S → T ⊆ V →
      (∀ p ∈ T, ‖p‖ ≤ R) → CoordinateBound P T 3 Z0 → CoordinateBound z T 3 Z →
      (∀ p ∈ T, ∀ sigma ∈ Icc (0 : ℝ) 1,
        c ≤ |stateQDenominator g (qHeightJetSegment P z sigma p)|) →
      ∀ i : Fin 6, ∀ p ∈ T,
        |comparisonCoefficient g P z i p| ≤ C ∧
        ∀ j : Fin 2, |coordPartial j (comparisonCoefficient g P z i) p| ≤
          C*(max 1 Z0+max 1 Z) := by
  classical
  let A := max R (max Z0 Z)
  choose C0 hC0 using fun i : Fin 6 => qCoefficient_uniform_derivative_bound hg hU hS hSU A hc i 0
  choose C1 hC1 using fun i : Fin 6 => qCoefficient_uniform_derivative_bound hg hU hS hSU A hc i 1
  let C := 1 + ∑ i : Fin 6, (max 0 (C0 i)+max 0 (C1 i))
  have hnon (i : Fin 6) : 0 ≤ max 0 (C0 i)+max 0 (C1 i) := by positivity
  have hCle : 1 ≤ C := by
    have hs : 0 ≤ ∑ i : Fin 6, (max 0 (C0 i)+max 0 (C1 i)) :=
      Finset.sum_nonneg (fun i _ => hnon i)
    dsimp [C]
    linarith
  have hC0le (i : Fin 6) : C0 i ≤ C := by
    have hi := Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)
    dsimp [C]
    linarith [le_max_right 0 (C0 i),le_max_left 0 (C1 i)]
  have hC1le (i : Fin 6) : C1 i ≤ C := by
    have hi := Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)
    dsimp [C]
    linarith [le_max_right 0 (C1 i),le_max_left 0 (C0 i)]
  refine ⟨C,hCle,?_⟩
  intro P z V T hV hVU hP hz hTS hTV hpB hPZ hzZ hfloor i p hp
  have hgV : SmoothPositiveOn g V := hg.mono hVU
  have h0 : ‖qSolutionJet P p‖ ≤ A :=
    (qSolutionJet_norm_bound_of_words hR (hpB p hp)
      (fun ds hds => hPZ ds (by omega) p hp)).trans
      (max_le_max le_rfl (le_max_left _ _))
  have h1 : ‖qSolutionJet z p‖ ≤ A :=
    (qSolutionJet_norm_bound_of_words hR (hpB p hp)
      (fun ds hds => hzZ ds (by omega) p hp)).trans
      (max_le_max le_rfl (le_max_right _ _))
  have htube (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      qHeightJetSegment P z sigma p ∈ qCompactTube g S A c := by
    refine ⟨⟨?_,?_⟩,hfloor p hp sigma hs⟩
    · change statePoint (qHeightJetSegment P z sigma p) ∈ S
      rw [statePoint_qHeightJetSegment]
      exact hTS hp
    · have hb := stateSegment_coord_bound hs
        (fun j => (norm_le_pi_norm (qSolutionJet P p) j).trans h0)
        (fun j => (norm_le_pi_norm (qSolutionJet z p) j).trans h1)
      exact ⟨fun j => (abs_le.mp (hb j)).1,fun j => (abs_le.mp (hb j)).2⟩
  have hseg (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g V := by
    have hd := qCompactTube_subset_domain hSU A hc (htube sigma hs)
    exact ⟨by simpa only [statePoint_qHeightJetSegment] using hTV hp,hd.2⟩
  have hval (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      |qFirstCoefficient g i (qHeightJetSegment P z sigma p)| ≤ C := by
    have hb := (hC0 i _ (htube sigma hs)).trans (hC0le i)
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hb
  have hder (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      ‖fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_one] using (hC1 i _ (htube sigma hs)).trans (hC1le i)
  constructor
  · change ‖∫ sigma in (0 : ℝ)..1,
        qFirstCoefficient g i (qHeightJetSegment P z sigma p)‖ ≤ C
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C)
      (f := fun sigma => qFirstCoefficient g i (qHeightJetSegment P z sigma p)) (by
        intro sigma hs
        have hs0 : sigma ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hs
        exact hval sigma ⟨hs0.1.le,hs0.2⟩)
    simpa only [sub_zero,abs_one,mul_one] using hb
  · intro j
    obtain ⟨W,hW,hpW,hWU,hWseg,_⟩ := exists_comparison_coefficient_neighborhood
      hgV hV hP hz isCompact_singleton (singleton_subset_iff.mpr (hTV hp))
      (fun _ hq sigma hs => by simpa only [mem_singleton_iff.mp hq] using hseg sigma hs)
    rw [comparisonCoefficient_partial hgV hV hP hz hW hWU hWseg (hpW (mem_singleton p)) i j,
      ← Real.norm_eq_abs]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C*(max 1 Z0+max 1 Z)) (f := fun sigma =>
        fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)
          ((1-sigma) • coordPartial j (qSolutionJet P) p+sigma • coordPartial j (qSolutionJet z) p)) ?_
    · simpa only [sub_zero,abs_one,mul_one] using hb
    intro sigma hs
    have hs' : sigma ∈ Icc (0 : ℝ) 1 := by
      have hs0 : sigma ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hs
      exact ⟨hs0.1.le,hs0.2⟩
    exact ((fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)).le_opNorm _).trans
      (mul_le_mul (hder sigma hs')
        (comparison_segment_direction_bound hV hP hz hTV hPZ hzZ hp hs' j)
        (norm_nonneg _) (zero_le_one.trans hCle))

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem metricComparisonSource_contDiffOn
    {g gRef : MetricField} {P z : Coord → ℝ} {V : Set Coord}
    (hg : SmoothPositiveOn g V) (hgRef : SmoothPositiveOn gRef V) (hV : IsOpen V)
    (hP : ContDiffOn ℝ ∞ P V) (hz : ContDiffOn ℝ ∞ z V)
    (hxx : ∀ p ∈ V, covHessian g z p 0 0 ≠ 0)
    (hrefz : ∀ p ∈ V, covHessian gRef z p 0 0 ≠ 0)
    (hrefP : ∀ p ∈ V, covHessian gRef P p 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (metricComparisonSource g gRef P z) V := by
  have hzJet := qSolutionJet_contDiffOn hV hz
  have hPJet := qSolutionJet_contDiffOn hV hP
  have hQ := (sixVariableQ_contDiffOn hg hV).comp hzJet
    (fun p hp => qSolutionJet_mem_domain hp (hxx p hp))
  have hQz := (sixVariableQ_contDiffOn hgRef hV).comp hzJet
    (fun p hp => qSolutionJet_mem_domain hp (hrefz p hp))
  have hQP := (sixVariableQ_contDiffOn hgRef hV).comp hPJet
    (fun p hp => qSolutionJet_mem_domain hp (hrefP p hp))
  exact (hQ.sub hQz).sub ((partial_contDiffOn (partial_contDiffOn hP hV 1) hV 1).sub hQP)

theorem exists_actual_comparison_energy
    {gRef : MetricField} {U S : Set Coord}
    (hgRef : SmoothPositiveOn gRef U) (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S ⊆ U)
    (R Z0 Z : ℝ) (hR : 0 ≤ R) {c s0 : ℝ} (hc : 0 < c) (hs0 : 0 < s0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (g : MetricField) (P z : Coord → ℝ) (V : Set Coord)
      (boxRadius width a b : ℝ),
      IsOpen V → V ⊆ U → SmoothPositiveOn g V →
      ContDiffOn ℝ ∞ P V → ContDiffOn ℝ ∞ z V →
      0 < width → width < boxRadius → a ≤ b →
      closedRectangle (-boxRadius) boxRadius a b ⊆ V →
      closedRectangle (-boxRadius) boxRadius a b ⊆ S →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, ‖p‖ ≤ R) →
      CoordinateBound P (closedRectangle (-boxRadius) boxRadius a b) 3 Z0 →
      CoordinateBound z (closedRectangle (-boxRadius) boxRadius a b) 3 Z →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b,
        (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p) →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, covHessian g z p 0 0 ≠ 0) →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, ∀ sigma ∈ Icc (0 : ℝ) 1,
        c ≤ |stateQDenominator gRef (qHeightJetSegment P z sigma p)| ∧
          s0 ≤ qFirstCoefficient gRef 5 (qHeightJetSegment P z sigma p)) →
      (∀ x ∈ Ioo (-boxRadius) boxRadius, P (boxPoint x a)=z (boxPoint x a)) →
      (∀ x ∈ Ioo (-boxRadius) boxRadius,
        coordPartial 1 P (boxPoint x a)=coordPartial 1 z (boxPoint x a)) →
      2*comparisonEnergySpeed C*(b-a)<2*width →
      Real.sqrt (movingEnergy (-width) width a (comparisonEnergySpeed C)
        (comparisonCoefficient gRef P z 5) (comparisonDifference P z) b) ≤
        Real.exp (comparisonEnergyRate C Z0 Z s0*(b-a))*
          ∫ t in a..b, movingSourceNorm (-width) width a (comparisonEnergySpeed C)
            (metricComparisonSource g gRef P z) t := by
  obtain ⟨C,hC,hbounds⟩ := exists_uniform_comparison_coefficient_bounds hgRef hU hS hSU R Z0 Z hR hc
  refine ⟨C,hC,?_⟩
  intro g P z V boxRadius width a b hV hVU hg hP hz hw hwR hab hboxV hboxS hpB hPZ hzZ
    hD hxx hmargin hvalue hvelocity hlength
  let T := closedRectangle (-boxRadius) boxRadius a b
  let speed := comparisonEnergySpeed C
  let MC := C*(max 1 Z0+max 1 Z)
  have hgRefV : SmoothPositiveOn gRef V := hgRef.mono hVU
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hs : 0 ≤ speed := add_nonneg hCp.le (Real.sqrt_nonneg _)
  have hMC : 0 ≤ MC := mul_nonneg hCp.le (by positivity)
  have hCmc : C ≤ MC := by
    have hsum : 1 ≤ max 1 Z0+max 1 Z := by
      linarith [le_max_left (1 : ℝ) Z0,le_max_left (1 : ℝ) Z]
    exact le_mul_of_one_le_right hCp.le hsum
  have hseg : ∀ p ∈ T, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef V := by
    intro p hp sigma hsigma
    refine ⟨by simpa only [statePoint_qHeightJetSegment] using hboxV hp,?_⟩
    exact abs_pos.mp (hc.trans_le (hmargin p hp sigma hsigma).1)
  obtain ⟨W,hW,hTW,hWV,hWseg,hcoeffSmooth⟩ := exists_comparison_coefficient_neighborhood
    hgRefV hV hP hz (closedRectangle_compact _ _ _ _) hboxV hseg
  let V0 := W ∩ (fun p => covHessian g z p 0 0) ⁻¹' ({0}ᶜ : Set ℝ)
  have hV0 : IsOpen V0 := ((covHessian_contDiffOn hg hV hz 0 0).continuousOn.mono hWV).isOpen_inter_preimage
    hW isClosed_singleton.isOpen_compl
  have hTV0 : T ⊆ V0 := fun p hp => ⟨hTW hp,hxx p hp⟩
  obtain ⟨radius,lo,hi,hRad,hlo,hhi,hrect⟩ := exists_containing_coordinateRectangle hV0
    (hw.trans hwR) hab hTV0
  let Rect := coordinateRectangle radius lo hi
  have hRect : IsOpen Rect := coordinateRectangle_isOpen _ _ _
  have hRectW : Rect ⊆ W := fun p hp => (hrect hp).1
  have hRectV : Rect ⊆ V := hRectW.trans hWV
  have hgsR : SmoothPositiveOn gRef Rect := hgRefV.mono hRectV
  have hgR : SmoothPositiveOn g Rect := hg.mono hRectV
  have hPR := hP.mono hRectV
  have hzR := hz.mono hRectV
  have hxR : ∀ p ∈ Rect, covHessian g z p 0 0 ≠ 0 := fun p hp => (hrect hp).2
  have hsegR : ∀ p ∈ Rect, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef Rect := by
    intro p hp sigma hsigma
    exact ⟨by simpa only [statePoint_qHeightJetSegment] using hp,(hWseg p (hRectW hp) sigma hsigma).2⟩
  have hrefP : ∀ p ∈ Rect, covHessian gRef P p 0 0 ≠ 0 := by
    intro p hp
    simpa only [qHeightJetSegment,stateSegment_zero,stateQDenominator_qSolutionJet] using
      (hsegR p hp 0 (by norm_num)).2
  have hrefz : ∀ p ∈ Rect, covHessian gRef z p 0 0 ≠ 0 := by
    intro p hp
    simpa only [qHeightJetSegment,stateSegment_one,stateQDenominator_qSolutionJet] using
      (hsegR p hp 1 (by norm_num)).2
  have hsource := metricComparisonSource_contDiffOn hgR hgsR hRect hPR hzR hxR hrefz hrefP
  have hcoeffR (i : Fin 6) : ContDiffOn ℝ ∞ (comparisonCoefficient gRef P z i) Rect :=
    (hcoeffSmooth i).mono hRectW
  have hnum := hbounds P z V T hV hVU hP hz hboxS hboxV hpB hPZ hzZ
    (fun p hp sigma hsigma => (hmargin p hp sigma hsigma).1)
  have hslabT : shrinkingSlab (-width) width a b speed ⊆ T := by
    intro p hp
    change p 1 ∈ Icc a b ∧ p 0 ∈ Icc (-width+speed*(p 1-a)) (width-speed*(p 1-a)) at hp
    have hinc : 0 ≤ speed*(p 1-a) := mul_nonneg hs (sub_nonneg.mpr hp.1.1)
    exact ⟨⟨by linarith [hp.2.1],
      by linarith [hp.2.2]⟩,hp.1⟩
  have hfloor (p : Coord) (hp : p ∈ shrinkingSlab (-width) width a b speed) :
      s0 ≤ comparisonCoefficient gRef P z 5 p :=
    averagedQCoefficient_lower hgRefV hV (hseg p (hslabT hp)) 5
      (fun sigma hsigma => (hmargin p (hslabT hp) sigma hsigma).2)
  have hchar (p : Coord) (hp : p ∈ shrinkingSlab (-width) width a b speed) :
      |comparisonCoefficient gRef P z 4 p|+Real.sqrt (comparisonCoefficient gRef P z 5 p) ≤ speed :=
    add_le_add (hnum 4 p (hslabT hp)).1
      (Real.sqrt_le_sqrt ((le_abs_self _).trans (hnum 5 p (hslabT hp)).1))
  have hEq (p : Coord) (hp : p ∈ shrinkingSlab (-width) width a b speed) :=
    comparison_equation_from_darboux hg hgRefV hV hz hP (hboxV (hslabT hp))
      (hD p (hslabT hp)) (hxx p (hslabT hp)) (hseg p (hslabT hp))
  have hprop := moving_slab_energy_propagation (hcoeffR 4) (hcoeffR 5) (hcoeffR 3) (hcoeffR 2)
    (hzR.sub hPR) hsource (hw.trans (hwR.trans hRad)) hab hs
    (by linarith) (by linarith) ⟨hlo,hab.trans_lt hhi⟩ ⟨hlo.trans_le hab,hhi⟩
    (by simpa only [sub_neg_eq_add,two_mul] using hlength) hs0 hMC hfloor
    (fun p hp => ⟨(hnum 3 p (hslabT hp)).1.trans hCmc,
      (hnum 2 p (hslabT hp)).1.trans hCmc,(hnum 4 p (hslabT hp)).2 0,
      (hnum 5 p (hslabT hp)).2 0,(hnum 5 p (hslabT hp)).2 1⟩) hchar hEq
  have hzero := comparison_initial_energy_zero (S := comparisonCoefficient gRef P z 5) hV hz hP
    (show -width ≤ width by linarith)
    (fun x hx => hboxV (by
      simpa [closedRectangle,boxPoint]
        using And.intro (And.intro hx.1.le hx.2.le) (And.intro (le_refl a) hab))) hvalue hvelocity
    (by linarith) hwR
  have hdiff : (fun x => z x-P x) = SmoothLocal.HighEquation.comparisonDifference P z := rfl
  rw [hdiff,hzero] at hprop
  simpa only [hzero,Real.sqrt_zero,zero_add,comparisonEnergyRate,MC] using hprop

end SmoothLocal.HighEquation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.HighEquation.exists_actual_comparison_energy := @OAI.SmoothLocal.HighEquation.exists_actual_comparison_energy
