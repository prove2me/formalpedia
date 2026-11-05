-- Prove2me | solution 1 for OAI.SmoothLocal.Flow.exists_C8_one_flow_physical_cap_estimates
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:50:06.600645+00:00
-- url     : https://prove2.me/submissions/bfd5bb05-439a-4053-adcd-7f9380f45fed

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport
import Theorems.Thm_OAI_SmoothLocal_Flow_exists_uniform_original_data_actual_high_cap_estimate

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
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

variable {f h : Coord → ℝ} {p : Coord} {U : Set Coord}

theorem coordPartial_div
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p)
    (hne : h p ≠ 0) (i : Fin 2) :
    coordPartial i (fun x => f x / h x) p =
      (coordPartial i f p * h p - f p * coordPartial i h p) / (h p) ^ 2 := by
  have hinv : HasFDerivAt (fun x : Coord => (h x)⁻¹)
      (-(h p ^ 2)⁻¹ • fderiv ℝ h p) p := by
    simpa only [Function.comp_def] using
      (hasDerivAt_inv hne).comp_hasFDerivAt p hh.hasFDerivAt
  have hquot : HasFDerivAt (fun x : Coord => f x / h x)
      (f p • (-(h p ^ 2)⁻¹ • fderiv ℝ h p) +
        (h p)⁻¹ • fderiv ℝ f p) p := by
    simpa only [div_eq_mul_inv] using hf.hasFDerivAt.fun_mul hinv
  unfold coordPartial
  rw [hquot.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  field_simp [hne]
  ring

theorem quotient_contDiffOn
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U)
    (hne : ∀ p ∈ U, h p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => f p / h p) U := by
  exact hf.div hh hne

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

theorem covectorNormSq_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    {z : Coord → ℝ} (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (covectorNormSq g z) U := by
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  exact ((inverseMetric_contDiffOn hg i j).mul (partial_contDiffOn hz hU i)).mul
    (partial_contDiffOn hz hU j)

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

theorem heightEnergy_contDiffOn {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (heightEnergy g z) U :=
  (metricDet_contDiffOn hg).mul (contDiffOn_const.sub (covectorNormSq_contDiffOn hg hU hz))

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
open Set
open scoped ContDiff

namespace SmoothLocal.Geometry
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {F : Coord → V} {U : Set Coord} {p : Coord}

theorem normed_coordPartial_contDiffOn (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (i : Fin 2) :
    ContDiffOn ℝ ∞ (coordPartial i F) U :=
  (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

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

theorem coordPartial_eventuallyEq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f h : Coord → V} {p : Coord} (heq : f =ᶠ[𝓝 p] h) (i : Fin 2) :
    coordPartial i f =ᶠ[𝓝 p] coordPartial i h := by
  filter_upwards [heq.eventuallyEq_nhds] with q hq
  exact coordPartial_eq_of_eventuallyEq hq i

theorem iteratedCoordPartial_eventuallyEq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f h : Coord → V} {p : Coord} (heq : f =ᶠ[𝓝 p] h) (dirs : List (Fin 2)) :
    iteratedCoordPartial dirs f =ᶠ[𝓝 p] iteratedCoordPartial dirs h := by
  induction dirs with
  | nil => exact heq
  | cons i is ih => exact coordPartial_eventuallyEq ih i

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def jetDriftVector (q : ℝ) : Coord := ![1, -q]

def christoffelAlongD (g : MetricField) (p : Coord) (q : ℝ) (i : Fin 2) : ℝ :=
  ∑ a, ∑ b, christoffel g i a b p * jetDriftVector q a * jetDriftVector q b

namespace DarbouxJetCalculus

theorem coordPartial_const (c : ℝ) (i : Fin 2) (u : Coord) :
    coordPartial i (fun _ : Coord => c) u = 0 := by
  simp [coordPartial]

theorem coordPartial_eval (i j : Fin 2) (u : Coord) :
    coordPartial i (fun v : Coord => v j) u = if j = i then 1 else 0 := by
  simp [coordPartial, (hasFDerivAt_apply j u).fderiv, Pi.single_apply]

theorem coordPartial_sq {f : Coord → ℝ} {u : Coord}
    (hf : DifferentiableAt ℝ f u) (i : Fin 2) :
    coordPartial i (fun v => (f v) ^ 2) u = 2 * f u * coordPartial i f u := by
  simp only [pow_two]
  rw [HessianCalculus.coordPartial_mul_at hf hf i]
  ring

end DarbouxJetCalculus

theorem jetConnection_differentiableAt (g : MetricField) (p u : Coord) (a b : Fin 2) :
    DifferentiableAt ℝ (jetConnection g p a b) u := by
  have h0 : DifferentiableAt ℝ (fun v : Coord => christoffel g 0 a b p * v 0) u :=
    (differentiableAt_apply (𝕜 := ℝ) 0 u).const_mul (christoffel g 0 a b p)
  have h1 : DifferentiableAt ℝ (fun v : Coord => christoffel g 1 a b p * v 1) u :=
    (differentiableAt_apply (𝕜 := ℝ) 1 u).const_mul (christoffel g 1 a b p)
  change DifferentiableAt ℝ (fun v => ∑ r, christoffel g r a b p * v r) u
  simpa only [Fin.sum_univ_two, Pi.add_def] using h0.add h1

theorem coordPartial_jetConnection (g : MetricField) (p u : Coord) (a b i : Fin 2) :
    coordPartial i (jetConnection g p a b) u = christoffel g i a b p := by
  have h0 : DifferentiableAt ℝ (fun v : Coord => christoffel g 0 a b p * v 0) u :=
    (differentiableAt_apply (𝕜 := ℝ) 0 u).const_mul (christoffel g 0 a b p)
  have h1 : DifferentiableAt ℝ (fun v : Coord => christoffel g 1 a b p * v 1) u :=
    (differentiableAt_apply (𝕜 := ℝ) 1 u).const_mul (christoffel g 1 a b p)
  change coordPartial i (fun v => ∑ r, christoffel g r a b p * v r) u = _
  simp only [Fin.sum_univ_two]
  rw [HessianCalculus.coordPartial_add_at h0 h1 i,
    HessianCalculus.coordPartial_mul_at (differentiableAt_const (christoffel g 0 a b p))
      (differentiableAt_apply (𝕜 := ℝ) 0 u) i,
    HessianCalculus.coordPartial_mul_at (differentiableAt_const (christoffel g 1 a b p))
      (differentiableAt_apply (𝕜 := ℝ) 1 u) i]
  fin_cases i <;>
    simp [DarbouxJetCalculus.coordPartial_const, DarbouxJetCalculus.coordPartial_eval]

theorem jetMixed_differentiableAt (g : MetricField) (p u : Coord) (b : ℝ) :
    DifferentiableAt ℝ (jetMixed g p b) u := by
  change DifferentiableAt ℝ (fun v => b - jetConnection g p 0 1 v) u
  simpa only [Pi.sub_def] using
    (differentiableAt_const (𝕜 := ℝ) b).sub (jetConnection_differentiableAt g p u 0 1)

theorem jetYY_differentiableAt (g : MetricField) (p u : Coord) (c : ℝ) :
    DifferentiableAt ℝ (jetYY g p c) u := by
  change DifferentiableAt ℝ (fun v => c - jetConnection g p 1 1 v) u
  simpa only [Pi.sub_def] using
    (differentiableAt_const (𝕜 := ℝ) c).sub (jetConnection_differentiableAt g p u 1 1)

theorem coordPartial_jetMixed (g : MetricField) (p u : Coord) (b : ℝ) (i : Fin 2) :
    coordPartial i (jetMixed g p b) u = -christoffel g i 0 1 p := by
  change coordPartial i (fun v => b - jetConnection g p 0 1 v) u = _
  rw [HessianCalculus.coordPartial_sub_at (differentiableAt_const b)
    (jetConnection_differentiableAt g p u 0 1) i]
  simp [DarbouxJetCalculus.coordPartial_const, coordPartial_jetConnection]

theorem coordPartial_jetYY (g : MetricField) (p u : Coord) (c : ℝ) (i : Fin 2) :
    coordPartial i (jetYY g p c) u = -christoffel g i 1 1 p := by
  change coordPartial i (fun v => c - jetConnection g p 1 1 v) u = _
  rw [HessianCalculus.coordPartial_sub_at (differentiableAt_const c)
    (jetConnection_differentiableAt g p u 1 1) i]
  simp [DarbouxJetCalculus.coordPartial_const, coordPartial_jetConnection]

theorem jetEnergy_differentiableAt (g : MetricField) (p u : Coord) :
    DifferentiableAt ℝ (jetEnergy g p) u := by
  have h0 := differentiableAt_apply (𝕜 := ℝ) 0 u
  have h1 := differentiableAt_apply (𝕜 := ℝ) 1 u
  change DifferentiableAt ℝ (fun v : Coord => (g p).det -
    (g p 1 1 * (v 0) ^ 2 - (g p 0 1 + g p 1 0) * v 0 * v 1 +
      g p 0 0 * (v 1) ^ 2)) u
  simpa only [Pi.pow_apply, Pi.add_def, Pi.sub_def, Pi.mul_apply] using
    (differentiableAt_const (𝕜 := ℝ) (g p).det).sub
    ((((h0.pow 2).const_mul (g p 1 1)).sub
      ((h0.const_mul (g p 0 1 + g p 1 0)).mul h1)).add
        ((h1.pow 2).const_mul (g p 0 0)))

theorem coordPartial_jetEnergy (g : MetricField) (p u : Coord) (i : Fin 2) :
    coordPartial i (jetEnergy g p) u =
      if i = 0 then -2 * g p 1 1 * u 0 + (g p 0 1 + g p 1 0) * u 1
      else (g p 0 1 + g p 1 0) * u 0 - 2 * g p 0 0 * u 1 := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) 0 u
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) 1 u
  have hQ := (((h0.fun_mul h0).const_mul (g p 1 1)).sub
    ((h0.const_mul (g p 0 1 + g p 1 0)).fun_mul h1)).add
      ((h1.fun_mul h1).const_mul (g p 0 0))
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (g p).det u).sub hQ
  simp only [Pi.add_def, Pi.sub_def] at hd
  change fderiv ℝ (fun v : Coord => (g p).det -
    (g p 1 1 * (v 0) ^ 2 - (g p 0 1 + g p 1 0) * v 0 * v 1 +
      g p 0 0 * (v 1) ^ 2)) u (Pi.single i 1) = _
  simp only [pow_two]
  rw [hd.fderiv]
  fin_cases i <;> simp <;> ring

theorem jetNumerator_differentiableAt (g : MetricField) (p u : Coord) (b : ℝ) :
    DifferentiableAt ℝ (jetNumerator g p b) u := by
  have hsq : DifferentiableAt ℝ (fun v => (jetMixed g p b v) ^ 2) u := by
    simpa only [pow_two] using
      ((jetMixed_differentiableAt g p u b).hasFDerivAt.fun_mul
        (jetMixed_differentiableAt g p u b).hasFDerivAt).differentiableAt
  have hKE : DifferentiableAt ℝ
      (fun v => gaussianCurvature g p * jetEnergy g p v) u :=
    (jetEnergy_differentiableAt g p u).const_mul (gaussianCurvature g p)
  change DifferentiableAt ℝ (fun v => (jetMixed g p b v) ^ 2 +
    gaussianCurvature g p * jetEnergy g p v) u
  simpa only [Pi.add_def] using hsq.add hKE

theorem coordPartial_jetNumerator (g : MetricField) (p u : Coord) (b : ℝ) (i : Fin 2) :
    coordPartial i (jetNumerator g p b) u =
      -2 * jetMixed g p b u * christoffel g i 0 1 p +
        gaussianCurvature g p * coordPartial i (jetEnergy g p) u := by
  have hsq : DifferentiableAt ℝ (fun v => (jetMixed g p b v) ^ 2) u := by
    simpa only [pow_two] using
      ((jetMixed_differentiableAt g p u b).hasFDerivAt.fun_mul
        (jetMixed_differentiableAt g p u b).hasFDerivAt).differentiableAt
  have hKE : DifferentiableAt ℝ
      (fun v => gaussianCurvature g p * jetEnergy g p v) u :=
    (jetEnergy_differentiableAt g p u).const_mul (gaussianCurvature g p)
  change coordPartial i (fun v => (jetMixed g p b v) ^ 2 +
    gaussianCurvature g p * jetEnergy g p v) u = _
  rw [HessianCalculus.coordPartial_add_at hsq hKE i,
    DarbouxJetCalculus.coordPartial_sq (jetMixed_differentiableAt g p u b) i,
    HessianCalculus.coordPartial_mul_at (differentiableAt_const (gaussianCurvature g p))
      (jetEnergy_differentiableAt g p u) i,
    coordPartial_jetMixed]
  simp only [DarbouxJetCalculus.coordPartial_const, zero_mul, zero_add]
  ring

theorem solvedDarboux_firstJet_expanded (g : MetricField) (p u : Coord) (b c : ℝ)
    (hne : jetYY g p c u ≠ 0) (i : Fin 2) :
    coordPartial i (solvedDarboux g p b c) u =
      christoffel g i 0 0 p - 2 * (jetMixed g p b u / jetYY g p c u) * christoffel g i 0 1 p +
        (jetMixed g p b u / jetYY g p c u) ^ 2 * christoffel g i 1 1 p +
        gaussianCurvature g p *
          (coordPartial i (jetEnergy g p) u / jetYY g p c u +
            jetEnergy g p u * christoffel g i 1 1 p / (jetYY g p c u) ^ 2) := by
  have hN := jetNumerator_differentiableAt g p u b
  have hH := jetYY_differentiableAt g p u c
  have hQ : DifferentiableAt ℝ
      (fun v => jetNumerator g p b v / jetYY g p c v) u := by
    simpa only [div_eq_mul_inv, Function.comp_def] using
      (hN.hasFDerivAt.fun_mul
        ((hasDerivAt_inv hne).comp_hasFDerivAt u hH.hasFDerivAt)).differentiableAt
  change coordPartial i (fun v => jetConnection g p 0 0 v +
    jetNumerator g p b v / jetYY g p c v) u = _
  rw [HessianCalculus.coordPartial_add_at (jetConnection_differentiableAt g p u 0 0) hQ i,
    coordPartial_jetConnection, coordPartial_div hN hH hne i,
    coordPartial_jetNumerator, coordPartial_jetYY]
  simp only [jetNumerator]
  field_simp [hne]
  ring

theorem christoffelAlongD_eq {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (q : ℝ) (i : Fin 2) :
    christoffelAlongD g p q i =
      christoffel g i 0 0 p - 2 * q * christoffel g i 0 1 p +
        q ^ 2 * christoffel g i 1 1 p := by
  simp only [christoffelAlongD, Fin.sum_univ_two, jetDriftVector,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [christoffel_lower_symm hg hU hp i 1 0]
  ring

theorem solvedDarboux_firstJet {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (u : Coord) (b c : ℝ) (hne : jetYY g p c u ≠ 0) (i : Fin 2) :
    coordPartial i (solvedDarboux g p b c) u =
      christoffelAlongD g p (jetMixed g p b u / jetYY g p c u) i +
        gaussianCurvature g p *
          (coordPartial i (jetEnergy g p) u / jetYY g p c u +
            jetEnergy g p u * christoffel g i 1 1 p / (jetYY g p c u) ^ 2) := by
  rw [christoffelAlongD_eq hg hU hp]
  exact solvedDarboux_firstJet_expanded g p u b c hne i

theorem solvedDarboux_deriv_b (g : MetricField) (p u : Coord) (b c : ℝ)
    (_hne : jetYY g p c u ≠ 0) :
    deriv (fun t => solvedDarboux g p t c u) b =
      2 * (jetMixed g p b u / jetYY g p c u) := by
  have hd := (((((hasDerivAt_id b).sub_const (jetConnection g p 0 1 u)).pow 2).add_const
    (gaussianCurvature g p * jetEnergy g p u)).div_const (jetYY g p c u)).const_add
      (jetConnection g p 0 0 u)
  simp only [Pi.pow_apply, id_eq] at hd
  change deriv (fun t => jetConnection g p 0 0 u +
    ((t - jetConnection g p 0 1 u) ^ 2 + gaussianCurvature g p * jetEnergy g p u) /
      jetYY g p c u) b = _
  rw [hd.deriv]
  simp only [jetMixed, mul_one]
  ring

theorem solvedDarboux_deriv_c (g : MetricField) (p u : Coord) (b c : ℝ)
    (hne : jetYY g p c u ≠ 0) :
    deriv (fun t => solvedDarboux g p b t u) c =
      -((jetMixed g p b u / jetYY g p c u) ^ 2 +
        gaussianCurvature g p * jetEnergy g p u / (jetYY g p c u) ^ 2) := by
  have hdH := (hasDerivAt_id c).sub_const (jetConnection g p 1 1 u)
  have hd := ((hasDerivAt_const c (jetNumerator g p b u)).div hdH hne).const_add
    (jetConnection g p 0 0 u)
  simp only [Pi.div_apply, id_eq] at hd
  change deriv (fun t => jetConnection g p 0 0 u +
    jetNumerator g p b u / (t - jetConnection g p 1 1 u)) c = _
  rw [hd.deriv]
  change (0 * jetYY g p c u - jetNumerator g p b u * 1) / (jetYY g p c u) ^ 2 = _
  simp only [jetNumerator]
  field_simp [hne]
  ring

theorem jetEnergy_at_height {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) (z : Coord → ℝ) :
    jetEnergy g p (fun i => coordPartial i z p) = heightEnergy g z p := by
  symm
  exact heightEnergy_polynomial z hg hp

theorem jetMixed_at_height (g : MetricField) (p : Coord) (z : Coord → ℝ) :
    jetMixed g p (coordPartial 0 (coordPartial 1 z) p) (fun i => coordPartial i z p) =
      covHessian g z p 0 1 := rfl

theorem jetYY_at_height (g : MetricField) (p : Coord) (z : Coord → ℝ) :
    jetYY g p (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p) =
      covHessian g z p 1 1 := rfl

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

theorem product_one (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (i : Fin 2) :
    iteratedCoordPartial [i] (fun x => a x * b x) p =
      iteratedCoordPartial [i] a p * b p + a p * iteratedCoordPartial [i] b p :=
  HessianCalculus.coordPartial_mul_at
    (iterated_differentiableAt ha hU hp []) (iterated_differentiableAt hb hU hp []) i

theorem product_two (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (i j : Fin 2) :
    iteratedCoordPartial [i, j] (fun x => a x * b x) p =
      iteratedCoordPartial [i, j] a p * b p +
      iteratedCoordPartial [j] a p * iteratedCoordPartial [i] b p +
      iteratedCoordPartial [i] a p * iteratedCoordPartial [j] b p +
      a p * iteratedCoordPartial [i, j] b p := by
  have he : coordPartial j (fun x => a x * b x) =ᶠ[𝓝 p]
      (fun x => coordPartial j a x * b x + a x * coordPartial j b x) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact product_one ha hb hU hx j
  change coordPartial i (coordPartial j (fun x => a x * b x)) p = _
  rw [coordPartial_eq_of_eventuallyEq he i]
  have ha0 := iterated_differentiableAt ha hU hp []
  have hb0 := iterated_differentiableAt hb hU hp []
  have haj := iterated_differentiableAt ha hU hp [j]
  have hbj := iterated_differentiableAt hb hU hp [j]
  have ht0 : DifferentiableAt ℝ (fun x => coordPartial j a x * b x) p := haj.mul hb0
  have ht1 : DifferentiableAt ℝ (fun x => a x * coordPartial j b x) p := ha0.mul hbj
  rw [HessianCalculus.coordPartial_add_at
      (f := fun x => coordPartial j a x * b x) (h := fun x => a x * coordPartial j b x) ht0 ht1 i,
    HessianCalculus.coordPartial_mul_at (f := coordPartial j a) (h := b) haj hb0 i,
    HessianCalculus.coordPartial_mul_at (f := a) (h := coordPartial j b) ha0 hbj i]
  dsimp [iteratedCoordPartial]
  ring

theorem product_three (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (i j k : Fin 2) :
    iteratedCoordPartial [i, j, k] (fun x => a x * b x) p =
      iteratedCoordPartial [i, j, k] a p * b p +
      iteratedCoordPartial [j, k] a p * iteratedCoordPartial [i] b p +
      iteratedCoordPartial [i, k] a p * iteratedCoordPartial [j] b p +
      iteratedCoordPartial [k] a p * iteratedCoordPartial [i, j] b p +
      iteratedCoordPartial [i, j] a p * iteratedCoordPartial [k] b p +
      iteratedCoordPartial [j] a p * iteratedCoordPartial [i, k] b p +
      iteratedCoordPartial [i] a p * iteratedCoordPartial [j, k] b p +
      a p * iteratedCoordPartial [i, j, k] b p := by
  have he : iteratedCoordPartial [j, k] (fun x => a x * b x) =ᶠ[𝓝 p]
      (fun x => iteratedCoordPartial [j, k] a x * b x +
        iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x +
        iteratedCoordPartial [j] a x * iteratedCoordPartial [k] b x +
        a x * iteratedCoordPartial [j, k] b x) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact product_two ha hb hU hx j k
  change coordPartial i (iteratedCoordPartial [j, k] (fun x => a x * b x)) p = _
  rw [coordPartial_eq_of_eventuallyEq he i]
  have ha0 := iterated_differentiableAt ha hU hp []
  have hb0 := iterated_differentiableAt hb hU hp []
  have haj := iterated_differentiableAt ha hU hp [j]
  have hak := iterated_differentiableAt ha hU hp [k]
  have hajk := iterated_differentiableAt ha hU hp [j, k]
  have hbj := iterated_differentiableAt hb hU hp [j]
  have hbk := iterated_differentiableAt hb hU hp [k]
  have hbjk := iterated_differentiableAt hb hU hp [j, k]
  have ht0 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j, k] a x * b x) p := hajk.mul hb0
  have ht1 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x) p := hak.mul hbj
  have ht2 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j] a x * iteratedCoordPartial [k] b x) p := haj.mul hbk
  have ht3 : DifferentiableAt ℝ (fun x => a x * iteratedCoordPartial [j, k] b x) p := ha0.mul hbjk
  have ht01 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j, k] a x * b x +
      iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x) p := ht0.add ht1
  have ht012 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j, k] a x * b x +
      iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x +
      iteratedCoordPartial [j] a x * iteratedCoordPartial [k] b x) p := ht01.add ht2
  rw [HessianCalculus.coordPartial_add_at
      ht012 ht3 i,
    HessianCalculus.coordPartial_add_at ht01 ht2 i,
    HessianCalculus.coordPartial_add_at ht0 ht1 i,
    HessianCalculus.coordPartial_mul_at (f := iteratedCoordPartial [j, k] a) (h := b) hajk hb0 i,
    HessianCalculus.coordPartial_mul_at (f := iteratedCoordPartial [k] a) (h := iteratedCoordPartial [j] b) hak hbj i,
    HessianCalculus.coordPartial_mul_at (f := iteratedCoordPartial [j] a) (h := iteratedCoordPartial [k] b) haj hbk i,
    HessianCalculus.coordPartial_mul_at (f := a) (h := iteratedCoordPartial [j, k] b) ha0 hbjk i]
  dsimp [iteratedCoordPartial]
  ring

theorem denominator_mul_quotient_word
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (ds : List (Fin 2)) :
    iteratedCoordPartial ds (fun x => b x * (a x / b x)) p =
      iteratedCoordPartial ds a p := by
  have he : (fun x => b x * (a x / b x)) =ᶠ[𝓝 p] a := by
    filter_upwards [hU.mem_nhds hp] with x hx
    field_simp [hne x hx]
  exact (iteratedCoordPartial_eventuallyEq he ds).self_of_nhds

theorem quotient_one (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (i : Fin 2) :
    iteratedCoordPartial [i] (fun x => a x / b x) p =
      (iteratedCoordPartial [i] a p -
        iteratedCoordPartial [i] b p * (a p / b p)) / b p := by
  have he := denominator_mul_quotient_word (a := a) hU hp hne [i]
  rw [product_one hb (quotient_contDiffOn ha hb hne) hU hp i] at he
  apply (eq_div_iff (hne p hp)).2
  nlinarith [he]

theorem quotient_two (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (i j : Fin 2) :
    iteratedCoordPartial [i, j] (fun x => a x / b x) p =
      (iteratedCoordPartial [i, j] a p -
        (iteratedCoordPartial [i, j] b p * (a p / b p) +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j] (fun x => a x / b x) p)) / b p := by
  have he := denominator_mul_quotient_word (a := a) hU hp hne [i, j]
  rw [product_two hb (quotient_contDiffOn ha hb hne) hU hp i j] at he
  apply (eq_div_iff (hne p hp)).2
  nlinarith [he]

theorem quotient_three (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (i j k : Fin 2) :
    iteratedCoordPartial [i, j, k] (fun x => a x / b x) p =
      (iteratedCoordPartial [i, j, k] a p -
        (iteratedCoordPartial [i, j, k] b p * (a p / b p) +
        iteratedCoordPartial [j, k] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i, k] b p * iteratedCoordPartial [j] (fun x => a x / b x) p +
        iteratedCoordPartial [k] b p * iteratedCoordPartial [i, j] (fun x => a x / b x) p +
        iteratedCoordPartial [i, j] b p * iteratedCoordPartial [k] (fun x => a x / b x) p +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i, k] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j, k] (fun x => a x / b x) p)) / b p := by
  have he := denominator_mul_quotient_word (a := a) hU hp hne [i, j, k]
  rw [product_three hb (quotient_contDiffOn ha hb hne) hU hp i j k] at he
  apply (eq_div_iff (hne p hp)).2
  nlinarith [he]

end LowQuotient
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem solvedDarboux_at_height
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    coordPartial 0 (coordPartial 0 z) p =
      solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p) := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  have hsolve : covHessian g z p 0 0 =
      ((covHessian g z p 0 1) ^ 2 + gaussianCurvature g p * heightEnergy g z p) /
        covHessian g z p 1 1 := by
    apply (eq_div_iff hyy).2
    linarith [hdet]
  change coordPartial 0 (coordPartial 0 z) p -
    jetConnection g p 0 0 (fun i => coordPartial i z p) = _ at hsolve
  rw [solvedDarboux, jetNumerator, jetMixed_at_height, jetYY_at_height,
    jetEnergy_at_height hg hp z]
  linarith [hsolve]

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

theorem hessianQuotient_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (hessianQuotient g z) U :=
  (covHessian_contDiffOn hg hU hz 0 1).div (covHessian_contDiffOn hg hU hz 1 1) hyy

theorem darbouxG_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (darbouxG g z) U :=
  (heightEnergy_contDiffOn hg hU hz).div ((covHessian_contDiffOn hg hU hz 1 1).pow 2)
    (fun p hp => pow_ne_zero 2 (hyy p hp))

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
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry.LowQuotient

theorem abs_add_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x + y| ≤ A + B := (abs_add_le x y).trans (add_le_add hx hy)

theorem abs_mul_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) (hA : 0 ≤ A) :
    |x * y| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) hA

theorem abs_sub_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x - y| ≤ A + B := (abs_sub x y).trans (add_le_add hx hy)

theorem abs_div_bound {x y N c : ℝ} (hN : 0 ≤ N) (hnum : |x| ≤ N)
    (hc : 0 < c) (hden : c ≤ |y|) : |x / y| ≤ N / c := by
  rw [abs_div]
  exact div_le_div₀ hN hnum hc hden

variable {U : Set Coord} {a b : Coord → ℝ} {M c : ℝ}

theorem denominator_ne_zero (hc : 0 < c) (hden : ∀ p ∈ U, c ≤ |b p|) :
    ∀ p ∈ U, b p ≠ 0 := by
  intro p hp hzero
  have hh := hden p hp
  rw [hzero, abs_zero] at hh
  linarith

theorem quotient_bound_zero (hM : 0 ≤ M) (hc : 0 < c)
    (ha0 : ∀ p ∈ U, |a p| ≤ M) (hden : ∀ p ∈ U, c ≤ |b p|)
    {p : Coord} (hp : p ∈ U) : |a p / b p| ≤ bound0 M c :=
  abs_div_bound hM (ha0 p hp) hc (hden p hp)

section SmoothQuotient
variable (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) (hU : IsOpen U)
variable (hM : 0 ≤ M) (hc : 0 < c)
variable (haB : ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U, |iteratedCoordPartial ds a p| ≤ M)
variable (hbB : ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U, |iteratedCoordPartial ds b p| ≤ M)
variable (hden : ∀ p ∈ U, c ≤ |b p|)
include ha hb hU hM hc haB hbB hden

theorem quotient_bound_one {p : Coord} (hp : p ∈ U) (i : Fin 2) :
    |iteratedCoordPartial [i] (fun x => a x / b x) p| ≤ bound1 M c := by
  rw [quotient_one ha hb hU hp (denominator_ne_zero hc hden) i]
  have hq0 := quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp
  apply abs_div_bound (by have := (bounds_nonneg hM hc).1; positivity) _ hc (hden p hp)
  exact abs_sub_bound (haB [i] (by norm_num) p hp)
    (abs_mul_bound (hbB [i] (by norm_num) p hp) hq0 hM)

theorem quotient_bound_two {p : Coord} (hp : p ∈ U) (i j : Fin 2) :
    |iteratedCoordPartial [i, j] (fun x => a x / b x) p| ≤ bound2 M c := by
  rw [quotient_two ha hb hU hp (denominator_ne_zero hc hden) i j]
  have hq0 := quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp
  have hqi := quotient_bound_one ha hb hU hM hc haB hbB hden hp i
  have hqj := quotient_bound_one ha hb hU hM hc haB hbB hden hp j
  have hterm0 := abs_mul_bound (hbB [i, j] (by norm_num) p hp) hq0 hM
  have htermi := abs_mul_bound (hbB [j] (by norm_num) p hp) hqi hM
  have htermj := abs_mul_bound (hbB [i] (by norm_num) p hp) hqj hM
  have hrest := abs_add_bound (abs_add_bound hterm0 htermi) htermj
  have hnum := abs_sub_bound (haB [i, j] (by norm_num) p hp) hrest
  have hnum' :
      |iteratedCoordPartial [i, j] a p -
        (iteratedCoordPartial [i, j] b p * (a p / b p) +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j] (fun x => a x / b x) p)| ≤
        M + M * bound0 M c + 2 * M * bound1 M c := by
    convert hnum using 1 <;> first | rfl | ring
  exact abs_div_bound (by obtain ⟨h0, h1, h2, h3⟩ := bounds_nonneg hM hc; positivity)
    hnum' hc (hden p hp)

theorem quotient_bound_three {p : Coord} (hp : p ∈ U) (i j k : Fin 2) :
    |iteratedCoordPartial [i, j, k] (fun x => a x / b x) p| ≤ bound3 M c := by
  rw [quotient_three ha hb hU hp (denominator_ne_zero hc hden) i j k]
  have hq0 := quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp
  have hqi := quotient_bound_one ha hb hU hM hc haB hbB hden hp i
  have hqj := quotient_bound_one ha hb hU hM hc haB hbB hden hp j
  have hqk := quotient_bound_one ha hb hU hM hc haB hbB hden hp k
  have hqij := quotient_bound_two ha hb hU hM hc haB hbB hden hp i j
  have hqik := quotient_bound_two ha hb hU hM hc haB hbB hden hp i k
  have hqjk := quotient_bound_two ha hb hU hM hc haB hbB hden hp j k
  have h0 := abs_mul_bound (hbB [i, j, k] (by norm_num) p hp) hq0 hM
  have h1 := abs_mul_bound (hbB [j, k] (by norm_num) p hp) hqi hM
  have h2 := abs_mul_bound (hbB [i, k] (by norm_num) p hp) hqj hM
  have h3 := abs_mul_bound (hbB [k] (by norm_num) p hp) hqij hM
  have h4 := abs_mul_bound (hbB [i, j] (by norm_num) p hp) hqk hM
  have h5 := abs_mul_bound (hbB [j] (by norm_num) p hp) hqik hM
  have h6 := abs_mul_bound (hbB [i] (by norm_num) p hp) hqjk hM
  have hrest := abs_add_bound (abs_add_bound (abs_add_bound (abs_add_bound
    (abs_add_bound (abs_add_bound h0 h1) h2) h3) h4) h5) h6
  have hnum := abs_sub_bound (haB [i, j, k] (by norm_num) p hp) hrest
  have hnum' :
      |iteratedCoordPartial [i, j, k] a p -
        (iteratedCoordPartial [i, j, k] b p * (a p / b p) +
        iteratedCoordPartial [j, k] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i, k] b p * iteratedCoordPartial [j] (fun x => a x / b x) p +
        iteratedCoordPartial [k] b p * iteratedCoordPartial [i, j] (fun x => a x / b x) p +
        iteratedCoordPartial [i, j] b p * iteratedCoordPartial [k] (fun x => a x / b x) p +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i, k] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j, k] (fun x => a x / b x) p)| ≤
        M + M * bound0 M c + 3 * M * bound1 M c + 3 * M * bound2 M c := by
    convert hnum using 1 <;> first | rfl | ring
  exact abs_div_bound (by obtain ⟨h0, h1, h2, h3⟩ := bounds_nonneg hM hc; positivity)
    hnum' hc (hden p hp)

theorem quotient_bound_through_three (ds : List (Fin 2)) (hlen : ds.length ≤ 3)
    {p : Coord} (hp : p ∈ U) :
    |iteratedCoordPartial ds (fun x => a x / b x) p| ≤ boundThroughThree M c := by
  obtain ⟨h0, h1, h2, h3⟩ := bounds_nonneg hM hc
  have hB0 : bound0 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree]; linarith
  have hB1 : bound1 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree]; linarith
  have hB2 : bound2 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree]; linarith
  have hB3 : bound3 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree]; linarith
  cases ds with
  | nil => exact (quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp).trans hB0
  | cons i ds =>
    cases ds with
    | nil => exact (quotient_bound_one ha hb hU hM hc haB hbB hden hp i).trans hB1
    | cons j ds =>
      cases ds with
      | nil => exact (quotient_bound_two ha hb hU hM hc haB hbB hden hp i j).trans hB2
      | cons k ds =>
        cases ds with
        | nil => exact (quotient_bound_three ha hb hU hM hc haB hbB hden hp i j k).trans hB3
        | cons l ds => simp only [List.length_cons] at hlen; omega

end SmoothQuotient
end SmoothLocal.Geometry.LowQuotient

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

theorem statePoint_solutionJet (z : Coord → ℝ) (p : Coord) :
    statePoint (solutionJet z p) = p := by
  ext i
  fin_cases i <;> rfl

theorem stateGradient_solutionJet (z : Coord → ℝ) (p : Coord) :
    stateGradient (solutionJet z p) = fun i => coordPartial i z p := by
  ext i
  fin_cases i <;> rfl

theorem stateDenominator_solutionJet (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    stateDenominator g (solutionJet z p) = covHessian g z p 1 1 := by
  unfold stateDenominator
  rw [statePoint_solutionJet, stateGradient_solutionJet]
  exact jetYY_at_height g p z

theorem sixVariableP_solutionJet (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    sixVariableP g (solutionJet z p) =
      solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p) := by
  unfold sixVariableP
  rw [statePoint_solutionJet, stateGradient_solutionJet]
  rfl

theorem solutionJet_contDiffOn {z : Coord → ℝ} (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (solutionJet z) U := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_apply ℝ ℝ 0 U
  · exact contDiffOn_apply ℝ ℝ 1 U
  · exact partial_contDiffOn hz hU 0
  · exact partial_contDiffOn hz hU 1
  · exact partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0
  · exact partial_contDiffOn (partial_contDiffOn hz hU 1) hU 1

theorem solutionJet_mem_domain (g : MetricField) (z : Coord → ℝ) {p : Coord}
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0) :
    solutionJet z p ∈ darbouxStateDomain g U := by
  constructor
  · simpa only [statePoint_solutionJet] using hp
  · simpa only [stateDenominator_solutionJet] using hyy

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

theorem boxPoint_mem {tl tr sb st t s : ℝ}
    (ht : t ∈ Icc tl tr) (hs : s ∈ Icc sb st) :
    boxPoint t s ∈ closedRectangle tl tr sb st := by
  simpa [boxPoint, closedRectangle] using And.intro ht hs

theorem boxPoint_hasDerivAt_t (t s : ℝ) :
    HasDerivAt (fun x => boxPoint x s) (Pi.single 0 (1 : ℝ) : Coord) t := by
  simpa [boxPoint] using
    ((hasDerivAt_id t).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add_const
      (s • (Pi.single 1 (1 : ℝ) : Coord))

theorem boxPoint_hasDerivAt_s (t s : ℝ) :
    HasDerivAt (boxPoint t) (Pi.single 1 (1 : ℝ) : Coord) s := by
  change HasDerivAt (fun x : ℝ => t • (Pi.single 0 (1 : ℝ) : Coord) +
    x • (Pi.single 1 (1 : ℝ) : Coord)) (Pi.single 1 (1 : ℝ) : Coord) s
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id s).smul_const (Pi.single 1 (1 : ℝ) : Coord)).const_add
      (t • (Pi.single 0 (1 : ℝ) : Coord))

variable {tl tr sb st : ℝ} {f g : Coord → ℝ}

theorem rectangle_area_integrable
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    IntegrableOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Ioc tl tr ×ˢ Ioc sb st) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Icc tl tr ×ˢ Icc sb st) :=
    hf.comp (by unfold boxPoint; fun_prop) (fun p hp => boxPoint_mem hp.1 hp.2)
  exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem rectangleIntegral_swap (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f =
      ∫ t in tl..tr, ∫ s in sb..st, f (boxPoint t s) := by
  have hi : IntegrableOn (Function.uncurry (fun t s => f (boxPoint t s)))
      (uIoc tl tr ×ˢ uIoc sb st) := by
    simpa only [uIoc_of_le ht, uIoc_of_le hs, Function.uncurry_def] using rectangle_area_integrable hf
  exact (intervalIntegral_intervalIntegral_swap hi).symm

theorem rectangleIntegral_eq_area (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f =
      ∫ p in Ioc tl tr ×ˢ Ioc sb st, f (boxPoint p.1 p.2) := by
  rw [rectangleIntegral_swap ht hs hf]
  simp_rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le hs]
  have hi : IntegrableOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Ioc tl tr ×ˢ Ioc sb st) (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod] using rectangle_area_integrable hf
  simpa only [← Measure.volume_eq_prod] using
    (setIntegral_prod (fun p : ℝ × ℝ => f (boxPoint p.1 p.2)) hi).symm

theorem rectangleIntegral_congr (ht : tl ≤ tr) (hs : sb ≤ st)
    (heq : EqOn f g (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f = rectangleIntegral tl tr sb st g := by
  unfold rectangleIntegral
  apply intervalIntegral.integral_congr
  intro s hs'
  apply intervalIntegral.integral_congr
  intro t ht'
  exact heq (boxPoint_mem
    (by simpa only [uIcc_of_le ht] using ht')
    (by simpa only [uIcc_of_le hs] using hs'))

variable {U : Set Coord}

end SmoothLocal.Weighted

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

theorem mono {f : Coord → ℝ} {U : Set Coord} {n m : ℕ} {M N : ℝ}
    (hf : CoordinateBound f U n M) (hm : m ≤ n) (hMN : M ≤ N) :
    CoordinateBound f U m N := fun ds hds p hp => (hf ds (hds.trans hm) p hp).trans hMN

theorem iterated_append (ds es : List (Fin 2)) (f : Coord → ℝ) :
    iteratedCoordPartial (ds ++ es) f = iteratedCoordPartial ds (iteratedCoordPartial es f) := by
  induction ds with
  | nil => rfl
  | cons i ds ih => simp only [List.cons_append, iteratedCoordPartial, ih]

theorem partial_bound {f : Coord → ℝ} {U : Set Coord} {n : ℕ} {M : ℝ}
    (hf : CoordinateBound f U (n + 1) M) (i : Fin 2) :
    CoordinateBound (coordPartial i f) U n M := by
  intro ds hds p hp
  have hh := hf (ds ++ [i]) (by simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right hds 1) p hp
  rw [iterated_append] at hh
  exact hh

theorem iterated_add {f h : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (ds : List (Fin 2)) {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds (fun x => f x + h x) p =
      iteratedCoordPartial ds f p + iteratedCoordPartial ds h p := by
  induction ds generalizing p with
  | nil => rfl
  | cons i ds ih =>
    have he : iteratedCoordPartial ds (fun x => f x + h x) =ᶠ[𝓝 p]
        (fun x => iteratedCoordPartial ds f x + iteratedCoordPartial ds h x) := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact ih hx
    change coordPartial i (iteratedCoordPartial ds (fun x => f x + h x)) p = _
    rw [coordPartial_eq_of_eventuallyEq he i]
    exact HessianCalculus.coordPartial_add_at
      (LowQuotient.iterated_differentiableAt hf hU hp ds)
      (LowQuotient.iterated_differentiableAt hh hU hp ds) i

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

theorem iterated_const_mul {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (c : ℝ)
    (ds : List (Fin 2)) {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds (fun x => c * f x) p = c * iteratedCoordPartial ds f p := by
  induction ds generalizing p with
  | nil => rfl
  | cons i ds ih =>
    have he : iteratedCoordPartial ds (fun x => c * f x) =ᶠ[𝓝 p]
        (fun x => c * iteratedCoordPartial ds f x) := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact ih hx
    change coordPartial i (iteratedCoordPartial ds (fun x => c * f x)) p = _
    rw [coordPartial_eq_of_eventuallyEq he i,
      HessianCalculus.coordPartial_mul_at (f := fun _ : Coord => c) (h := iteratedCoordPartial ds f)
        (differentiableAt_const c)
        (LowQuotient.iterated_differentiableAt hf hU hp ds) i]
    simp [coordPartial, iteratedCoordPartial]

theorem add {f h : Coord → ℝ} {U : Set Coord} {n : ℕ} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hfB : CoordinateBound f U n A) (hhB : CoordinateBound h U n B) :
    CoordinateBound (fun x => f x + h x) U n (A + B) := by
  intro ds hds p hp
  rw [iterated_add hf hh hU ds hp]
  exact (abs_add_le _ _).trans (add_le_add (hfB ds hds p hp) (hhB ds hds p hp))

theorem sub {f h : Coord → ℝ} {U : Set Coord} {n : ℕ} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hfB : CoordinateBound f U n A) (hhB : CoordinateBound h U n B) :
    CoordinateBound (fun x => f x - h x) U n (A + B) := by
  intro ds hds p hp
  rw [iterated_sub hf hh hU ds hp]
  exact (abs_sub _ _).trans (add_le_add (hfB ds hds p hp) (hhB ds hds p hp))

theorem const_mul {f : Coord → ℝ} {U : Set Coord} {n : ℕ} {A : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hfB : CoordinateBound f U n A) (c : ℝ) :
    CoordinateBound (fun x => c * f x) U n (|c| * A) := by
  intro ds hds p hp
  rw [iterated_const_mul hf hU c ds hp, abs_mul]
  exact mul_le_mul_of_nonneg_left (hfB ds hds p hp) (abs_nonneg c)

theorem neg {f : Coord → ℝ} {U : Set Coord} {n : ℕ} {A : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hfB : CoordinateBound f U n A) :
    CoordinateBound (fun x => -f x) U n A := by
  simpa only [neg_one_mul, abs_neg, abs_one, one_mul] using const_mul hf hU hfB (-1)

theorem abs_add_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x + y| ≤ A + B := (abs_add_le x y).trans (add_le_add hx hy)

theorem mul_through_three {f h : Coord → ℝ} {U : Set Coord} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfB : CoordinateBound f U 3 A) (hhB : CoordinateBound h U 3 B) :
    CoordinateBound (fun x => f x * h x) U 3 (8 * A * B) := by
  intro ds hds p hp
  have hab (vs ws : List (Fin 2)) (hv : vs.length ≤ 3) (hw : ws.length ≤ 3) :
      |iteratedCoordPartial vs f p * iteratedCoordPartial ws h p| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul (hfB vs hv p hp) (hhB ws hw p hp) (abs_nonneg _) hA
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  cases ds with
  | nil =>
    exact (hab [] [] (by norm_num) (by norm_num)).trans (by nlinarith)
  | cons i ds =>
    cases ds with
    | nil =>
      rw [LowQuotient.product_one hf hh hU hp i]
      exact (abs_add_bound (hab [i] [] (by norm_num) (by norm_num))
        (hab [] [i] (by norm_num) (by norm_num))).trans (by nlinarith)
    | cons j ds =>
      cases ds with
      | nil =>
        rw [LowQuotient.product_two hf hh hU hp i j]
        exact (abs_add_bound (abs_add_bound (abs_add_bound
          (hab [i, j] [] (by norm_num) (by norm_num))
          (hab [j] [i] (by norm_num) (by norm_num)))
          (hab [i] [j] (by norm_num) (by norm_num)))
          (hab [] [i, j] (by norm_num) (by norm_num))).trans (by nlinarith)
      | cons k ds =>
        cases ds with
        | nil =>
          rw [LowQuotient.product_three hf hh hU hp i j k]
          have hsum := abs_add_bound (abs_add_bound (abs_add_bound (abs_add_bound
            (abs_add_bound (abs_add_bound (abs_add_bound
            (hab [i, j, k] [] (by norm_num) (by norm_num))
            (hab [j, k] [i] (by norm_num) (by norm_num)))
            (hab [i, k] [j] (by norm_num) (by norm_num)))
            (hab [k] [i, j] (by norm_num) (by norm_num)))
            (hab [i, j] [k] (by norm_num) (by norm_num)))
            (hab [j] [i, k] (by norm_num) (by norm_num)))
            (hab [i] [j, k] (by norm_num) (by norm_num)))
            (hab [] [i, j, k] (by norm_num) (by norm_num))
          convert hsum using 1 <;> first | rfl | ring
        | cons l ds => simp only [List.length_cons] at hds; omega

end CoordinateBound
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

def solutionJetCurve (z : Coord → ℝ) (x : ℝ) : ℝ → DarbouxState :=
  fun y => solutionJet z ![x, y]

theorem verticalPoint_contDiff (x : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ => (![x, y] : Coord)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_id

theorem solutionJetCurve_contDiffAt {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U) :
    ContDiffAt ℝ ∞ (solutionJetCurve z x) y :=
  ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).comp y
    (verticalPoint_contDiff x).contDiffAt

theorem sixVariableP_contDiffAt_solutionJet
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    ContDiffAt ℝ ∞ (sixVariableP g) (solutionJet z p) :=
  (sixVariableP_contDiffOn hg hU).contDiffAt
    ((darbouxStateDomain_isOpen hg hU).mem_nhds (solutionJet_mem_domain g z hp hyy))

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Matrix BigOperators

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem heightPFirst_eq
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    heightPFirst g z i p = christoffelAlongD g p (hessianQuotient g z p) i +
      gaussianCurvature g p *
        (coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) / covHessian g z p 1 1 +
          heightEnergy g z p * christoffel g i 1 1 p / (covHessian g z p 1 1) ^ 2) := by
  simpa only [heightPFirst, jetMixed_at_height, jetYY_at_height,
    jetEnergy_at_height hg hp z, hessianQuotient] using
    solvedDarboux_firstJet hg hU hp (fun r => coordPartial r z p)
      (coordPartial 0 (coordPartial 1 z) p) (coordPartial 1 (coordPartial 1 z) p) hyy i

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

variable {B : Coord → ℝ} {R a b : ℝ}

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {M c : ℝ}

theorem hessianQuotient_coordinate_bound_through_three
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hM : 0 ≤ M) (hc : 0 < c)
    (hH : ∀ i j : Fin 2, ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U,
      |iteratedCoordPartial ds (fun x => covHessian g z x i j) p| ≤ M)
    (hden : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) :
    ContDiffOn ℝ ∞ (hessianQuotient g z) U ∧
      ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U,
        |iteratedCoordPartial ds (hessianQuotient g z) p| ≤ LowQuotient.boundThroughThree M c := by
  have hxy := covHessian_contDiffOn hg hU hz 0 1
  have hyy := covHessian_contDiffOn hg hU hz 1 1
  refine ⟨hessianQuotient_contDiffOn hg hU hz (LowQuotient.denominator_ne_zero hc hden), ?_⟩
  intro ds hlen p hp
  exact LowQuotient.quotient_bound_through_three hxy hyy hU hM hc (hH 0 1) (hH 1 1) hden ds hlen hp

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

open SmoothLocal.Geometry

variable {A B C v u f : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem rectangleIntegral_const_mul (tl tr sb st c : ℝ) (g : Coord → ℝ) :
    rectangleIntegral tl tr sb st (fun p => c * g p) = c * rectangleIntegral tl tr sb st g := by
  unfold rectangleIntegral
  simp only [intervalIntegral.integral_const_mul]

variable {tl tr sb st : ℝ}

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

def coordinateDirections : (ds : List (Fin 2)) → Fin ds.length → Coord
  | [] => fun _ => 0
  | i :: ds => Fin.cons (Pi.single i 1) (coordinateDirections ds)

theorem coordinateDirections_norm (ds : List (Fin 2)) (k : Fin ds.length) :
    ‖coordinateDirections ds k‖ = 1 := by
  induction ds with
  | nil => exact Fin.elim0 k
  | cons i ds ih =>
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [coordinateDirections, Pi.norm_single]
    · simpa only [coordinateDirections, Fin.cons_succ] using ih j

theorem iteratedCoordPartial_eq_jet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ds : List (Fin 2))
    {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds f p = iteratedFDeriv ℝ ds.length f p (coordinateDirections ds) := by
  induction ds generalizing p with
  | nil => rfl
  | cons i ds ih =>
    have he : iteratedCoordPartial ds f =ᶠ[𝓝 p]
        (fun x => iteratedFDeriv ℝ ds.length f x (coordinateDirections ds)) := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact ih hx
    change coordPartial i (iteratedCoordPartial ds f) p = _
    rw [coordPartial_eq_of_eventuallyEq he i]
    have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl ds.length)
    simp only [List.length_cons]
    rw [hd.iteratedFDeriv_succ_apply_left']
    rfl

theorem norm_iteratedCoordPartial_le_jet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ds : List (Fin 2))
    {p : Coord} (hp : p ∈ U) :
    ‖iteratedCoordPartial ds f p‖ ≤ ‖iteratedFDeriv ℝ ds.length f p‖ := by
  rw [iteratedCoordPartial_eq_jet hf hU ds hp]
  simpa only [coordinateDirections_norm, Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ ds.length f p).le_opNorm (coordinateDirections ds)

theorem coordinateBound_of_frechet_bounds {f : Coord → ℝ} {U S : Set Coord} {n : ℕ} {M : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hSU : S ⊆ U)
    (hB : ∀ k ≤ n, ∀ p ∈ S, ‖iteratedFDeriv ℝ k f p‖ ≤ M) :
    CoordinateBound f S n M := by
  intro ds hds p hp
  exact (norm_iteratedCoordPartial_le_jet hf hU ds (hSU hp)).trans (hB ds.length hds p hp)

theorem coordinateBound_five_of_frechet_eight {f : Coord → ℝ} {U S : Set Coord} {M : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hSU : S ⊆ U)
    (hB : ∀ k ≤ 8, ∀ p ∈ S, ‖iteratedFDeriv ℝ k f p‖ ≤ M) :
    CoordinateBound f S 5 M :=
  (coordinateBound_of_frechet_bounds hf hU hSU hB).mono (by norm_num) le_rfl

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

theorem verticalJet_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∀ n, ContDiffOn ℝ ∞ (verticalJet f n) U := by
  intro n
  induction n with
  | zero => exact hf
  | succ n hn => exact normed_coordPartial_contDiffOn hn hU 1

theorem verticalPoint_hasDerivAt (x y : ℝ) :
    HasDerivAt (fun t : ℝ => (![x, t] : Coord)) (Pi.single 1 (1 : ℝ)) y := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa using hasDerivAt_const y x
  · convert hasDerivAt_id y using 1 <;> rfl

theorem verticalJet_slice_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (n : ℕ)
    (hp : (![x, y] : Coord) ∈ U) :
    HasDerivAt (fun t => verticalJet f n ![x, t]) (verticalJet f (n + 1) ![x, y]) y := by
  have hd : DifferentiableAt ℝ (verticalJet f n) ![x, y] :=
    (((verticalJet_contDiffOn hU hf n).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
  exact hd.hasFDerivAt.comp_hasDerivAt y (verticalPoint_hasDerivAt x y)

theorem verticalJet_slice
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (x : ℝ) : ∀ n y, (![x, y] : Coord) ∈ U →
      iteratedDeriv n (fun t => f ![x, t]) y = verticalJet f n ![x, y] := by
  intro n
  induction n with
  | zero => intro y hy; rfl
  | succ n hn =>
    intro y hy
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun t => f ![x, t]) =ᶠ[𝓝 y]
        (fun t => verticalJet f n ![x, t]) := by
      filter_upwards [(hU.preimage (verticalPoint_contDiff x).continuous).mem_nhds hy] with t ht
      exact hn t ht
    rw [heq.deriv_eq]
    exact (verticalJet_slice_hasDerivAt hU hf n hy).deriv

theorem verticalJet_coordPartial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (i : Fin 2) : ∀ n p, p ∈ U →
      verticalJet (coordPartial i f) n p = coordPartial i (verticalJet f n) p := by
  intro n
  induction n with
  | zero => intro p hp; rfl
  | succ n hn =>
    intro p hp
    have heq : verticalJet (coordPartial i f) n =ᶠ[𝓝 p] coordPartial i (verticalJet f n) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hn q hq
    have hd : coordPartial 1 (verticalJet (coordPartial i f) n) p =
        coordPartial 1 (coordPartial i (verticalJet f n)) p := by
      exact congrArg (fun L : Coord →L[ℝ] V => L (Pi.single 1 1)) heq.fderiv_eq
    change coordPartial 1 (verticalJet (coordPartial i f) n) p =
      coordPartial i (coordPartial 1 (verticalJet f n)) p
    rw [hd]
    exact coordPartial_comm (verticalJet_contDiffOn hU hf n) hU hp 1 i

theorem verticalJet_two_coordPartials
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hp : p ∈ U) (n : ℕ) (i j : Fin 2) :
    verticalJet (coordPartial i (coordPartial j f)) n p =
      coordPartial i (coordPartial j (verticalJet f n)) p := by
  rw [verticalJet_coordPartial hU (normed_coordPartial_contDiffOn hf hU j) i n p hp]
  have heq : verticalJet (coordPartial j f) n =ᶠ[𝓝 p] coordPartial j (verticalJet f n) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact verticalJet_coordPartial hU hf j n q hq
  exact congrArg (fun L : Coord →L[ℝ] V => L (Pi.single i 1)) heq.fderiv_eq

theorem iteratedDeriv_state_eval {f : ℝ → DarbouxState} {y : ℝ}
    (hf : ContDiffAt ℝ ∞ f y) (n : ℕ) (i : Fin 6) :
    (iteratedDeriv n f y) i = iteratedDeriv n (fun t => f t i) y := by
  let L : DarbouxState →L[ℝ] ℝ := ContinuousLinearMap.proj i
  symm
  change iteratedFDeriv ℝ n (L ∘ f) y (fun _ => 1) = L (iteratedDeriv n f y)
  rw [L.iteratedFDeriv_comp_left hf (WithTop.coe_le_coe.mpr le_top)]
  rfl

theorem solutionJetCurve_iteratedDeriv
    {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U)
    (n : ℕ) (hn : 2 ≤ n) :
    iteratedDeriv n (solutionJetCurve z x) y =
      ![0, 0, coordPartial 0 (verticalJet z n) ![x, y],
        coordPartial 1 (verticalJet z n) ![x, y],
        coordPartial 0 (coordPartial 1 (verticalJet z n)) ![x, y],
        coordPartial 1 (coordPartial 1 (verticalJet z n)) ![x, y]] := by
  have hc := solutionJetCurve_contDiffAt hU hz hp
  ext i
  rw [iteratedDeriv_state_eval hc n i]
  fin_cases i
  · change iteratedDeriv n (fun _ : ℝ => x) y = 0
    simp [iteratedDeriv_const, show n ≠ 0 by omega]
  · change iteratedDeriv n id y = 0
    simp [iteratedDeriv_id, show n ≠ 0 by omega, show n ≠ 1 by omega]
  · change iteratedDeriv n (fun t => coordPartial 0 z ![x, t]) y = _
    rw [verticalJet_slice hU (normed_coordPartial_contDiffOn hz hU 0) x n y hp,
      verticalJet_coordPartial hU hz 0 n ![x, y] hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 z ![x, t]) y = _
    rw [verticalJet_slice hU (normed_coordPartial_contDiffOn hz hU 1) x n y hp,
      verticalJet_coordPartial hU hz 1 n ![x, y] hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 1 z) ![x, t]) y = _
    rw [verticalJet_slice hU (normed_coordPartial_contDiffOn (normed_coordPartial_contDiffOn hz hU 1) hU 0) x n y hp,
      verticalJet_two_coordPartials hU hz hp n 0 1]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 (coordPartial 1 z) ![x, t]) y = _
    rw [verticalJet_slice hU (normed_coordPartial_contDiffOn (normed_coordPartial_contDiffOn hz hU 1) hU 1) x n y hp,
      verticalJet_two_coordPartials hU hz hp n 1 1]
    rfl

end SmoothLocal.HighEquation

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

theorem pairPrimitive_continuousOn {B : ℝ × ℝ → ℝ} {R a b : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) :
    ContinuousOn (pairPrimitive B) (pairRectangle R a b) := by
  intro p hp
  obtain ⟨r, hr, hrR, hpr⟩ := exists_compact_time_interval hp.1
  have hF := (primitiveCLM r hr).continuous.comp_continuousOn
    (pairCompactFamily_continuousOn hB hrR)
  have hc := intervalExtension_family_continuousOn r hr hF
  have hn : (univ : Set ℝ) ×ˢ Ioo a b ∈ 𝓝 p :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hp.2⟩
  have he : pairPrimitive B =ᶠ[𝓝 p]
      (fun q => intervalExtension r hr (primitiveCLM r hr (pairCompactFamily B r q.2)) q.1) := by
    filter_upwards [(pairRectangle_isOpen r a b).mem_nhds ⟨hpr, hp.2⟩] with q hq
    exact pairPrimitive_eq_clamped hB hr hrR hq.1 hq.2
  exact ((hc.continuousAt hn).congr_of_eventuallyEq he).continuousWithinAt

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

theorem pairPrimitive_hasDerivAt_x {B : ℝ × ℝ → ℝ} {R a b x y : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b))
    (hx : x ∈ Ioo (-R) R) (hy : y ∈ Ioo a b) :
    HasDerivAt (fun t => pairPrimitive B (t, y)) (B (x, y)) x := by
  obtain ⟨r, hr, hrR, hxr⟩ := exists_compact_time_interval hx
  have hd := intervalExtension_primitive_hasDerivAt r hr (pairCompactFamily B r y) hxr
  rw [intervalExtension_apply_of_mem r hr _ ⟨hxr.1.le, hxr.2.le⟩,
    pairCompactFamily_apply hB hrR hy] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hxr] with t ht
  exact pairPrimitive_eq_clamped hB hr hrR ht hy

theorem pairPrimitive_contDiffOn_nat (n : ℕ) {B : ℝ × ℝ → ℝ} {R a b : ℝ}
    (hB : ContDiffOn ℝ n B (pairRectangle R a b)) :
    ContDiffOn ℝ n (pairPrimitive B) (pairRectangle R a b) := by
  induction n generalizing B with
  | zero =>
      simpa only [Nat.cast_zero, contDiffOn_zero] using pairPrimitive_continuousOn hB.continuousOn
  | succ n hn =>
      have hB1 : ContDiffOn ℝ 1 B (pairRectangle R a b) := hB.of_le (by simp)
      apply contDiffOn_succ_of_continuous_partials (pairRectangle_isOpen R a b) n
        (hB.of_le (by simp)) (hn (pairPartialY_contDiffOn n hB))
      · intro p hp
        exact pairPrimitive_hasDerivAt_x hB.continuousOn hp.1 hp.2
      · intro p hp
        exact pairPrimitive_hasDerivAt_y hB1 hp.1 hp.2

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation

def chainTerm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (w : ChainWord) (t : ℝ) : ℝ :=
  iteratedFDeriv ℝ w.arity F (J t) (fun i => iteratedDeriv (w.order i) J t)

theorem iteratedDeriv_contDiffAt_infty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : ℝ → E} {t : ℝ} (hJ : ContDiffAt ℝ ∞ J t) :
    ∀ n, ContDiffAt ℝ ∞ (iteratedDeriv n J) t := by
  intro n
  induction n with
  | zero => simpa using hJ
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact hn.derivWithin (by simp)

theorem iteratedDeriv_hasDerivAt_infty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : ℝ → E} {t : ℝ} (hJ : ContDiffAt ℝ ∞ J t) (n : ℕ) :
    HasDerivAt (iteratedDeriv n J) (iteratedDeriv (n + 1) J t) t := by
  rw [iteratedDeriv_succ]
  exact ((iteratedDeriv_contDiffAt_infty hJ n).differentiableAt (by simp)).hasDerivAt

theorem chainTerm_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t) (w : ChainWord) :
    HasDerivAt (chainTerm F J w)
      (chainTerm F J w.prepend t + ∑ i, chainTerm F J (w.bump i) t) t := by
  have hJ0 : HasDerivAt J (iteratedDeriv 1 J t) t := by
    simpa using iteratedDeriv_hasDerivAt_infty hJ 0
  have houter := (hF.differentiableAt_iteratedFDeriv (m := w.arity)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl w.arity)).hasFDerivAt
    |>.comp_hasDerivAt t hJ0
  have h := houter.hasFDerivAt.continuousMultilinearMap_apply
    (fun i => (iteratedDeriv_hasDerivAt_infty hJ (w.order i)).hasFDerivAt)
    |>.hasDerivAt
  convert h using 1 <;> try rfl
  simp only [chainTerm, ChainWord.prepend, ChainWord.bump,
    add_apply, ContinuousLinearMap.comp_apply,
    sum_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul,
    ContinuousMultilinearMap.apply_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change (iteratedFDeriv ℝ w.arity F (J t))
      (fun j => iteratedDeriv (Function.update w.order i (w.order i + 1) j) J t) =
    (iteratedFDeriv ℝ w.arity F (J t))
      (Function.update (fun j => iteratedDeriv (w.order j) J t) i (iteratedDeriv (w.order i + 1) J t))
  congr 1
  funext j
  by_cases hj : j = i
  · subst j; simp
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem modelSquare_isCompact : IsCompact modelSquare := isCompact_Icc

theorem coordinatePoint_mem_modelSquare {t y : ℝ}
    (ht : t ∈ Icc (-3 : ℝ) 3) (hy : y ∈ Icc (-3 : ℝ) 3) :
    coordinatePoint t y ∈ modelSquare := by
  simp only [mem_Icc] at ht hy
  constructor <;> intro i <;> fin_cases i <;> simp [coordinatePoint] <;> tauto

def flowField (q : Coord → ℝ) (t y : ℝ) : ℝ := -q (coordinatePoint t y)

variable {q : Coord → ℝ} {U : Set Coord}

theorem flowField_hasDerivAt_y (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U)
    {t y : ℝ} (hp : coordinatePoint t y ∈ U) :
    HasDerivAt (flowField q t) (-coordPartial 1 q (coordinatePoint t y)) y := by
  have hd := (hq.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact (hd.hasFDerivAt.comp_hasDerivAt y (coordinatePoint_hasDerivAt_y t y)).neg

theorem exists_flowField_lipschitz (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U)
    (hSU : modelSquare ⊆ U) :
    ∃ L : ℝ≥0, ∀ t ∈ Icc (-2 : ℝ) 2,
      LipschitzOnWith L (flowField q t) (closedBall (0 : ℝ) 3) := by
  have hc : ContinuousOn (coordPartial 1 q) modelSquare :=
    (partial_contDiffOn hq hU 1).continuousOn.mono hSU
  obtain ⟨M, hM⟩ := modelSquare_isCompact.exists_bound_of_continuousOn hc
  let L : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  refine ⟨L, ?_⟩
  intro t ht
  have hmem (y : ℝ) (hy : y ∈ closedBall (0 : ℝ) 3) :
      coordinatePoint t y ∈ modelSquare := by
    have hy' : |y| ≤ 3 := by simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hy
    exact coordinatePoint_mem_modelSquare ⟨by linarith [ht.1], by linarith [ht.2]⟩ (abs_le.mp hy')
  apply (convex_closedBall (0 : ℝ) 3).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun y hy => (flowField_hasDerivAt_y hq hU (hSU (hmem y hy))).hasDerivWithinAt)
  intro y hy
  change ‖-coordPartial 1 q (coordinatePoint t y)‖ ≤ max M 0
  rw [norm_neg]
  exact (hM _ (hmem y hy)).trans (le_max_left _ _)

theorem exists_cap_picard (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U)
    (hSU : modelSquare ⊆ U) (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100) :
    ∃ L : ℝ≥0, IsPicardLindelof (flowField q)
      (⟨0, by norm_num⟩ : Icc (-2 : ℝ) 2) 0 3 2 (1 / 100) L := by
  obtain ⟨L, hL⟩ := exists_flowField_lipschitz hq hU hSU
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · intro y hy
    have hy' : |y| ≤ 3 := by simpa only [mem_closedBall, Real.dist_eq, sub_zero,
      NNReal.coe_ofNat] using hy
    exact hq.continuousOn.neg.comp (by unfold coordinatePoint; fun_prop)
      (fun t ht => hSU (coordinatePoint_mem_modelSquare
        ⟨by linarith [ht.1], by linarith [ht.2]⟩ (abs_le.mp hy')))
  · intro t ht y hy
    have hy' : |y| ≤ 3 := by simpa only [mem_closedBall, Real.dist_eq, sub_zero,
      NNReal.coe_ofNat] using hy
    have hm := coordinatePoint_mem_modelSquare (t := t) (y := y)
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ (abs_le.mp hy')
    simpa only [flowField, norm_neg, Real.norm_eq_abs, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat] using hsmall _ hm
  · norm_num

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord} {G d : ℝ}

theorem metricDet_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G) :
    CoordinateBound (fun p => (g p).det) U 3 (16 * G^2) := by
  have hdiag := CoordinateBound.mul_through_three (hg.1 0 0) (hg.1 1 1) hU hG hG (hgB 0 0) (hgB 1 1)
  have hoff := CoordinateBound.mul_through_three (hg.1 0 1) (hg.1 1 0) hU hG hG (hgB 0 1) (hgB 1 0)
  have hdet := CoordinateBound.sub ((hg.1 0 0).mul (hg.1 1 1))
    ((hg.1 0 1).mul (hg.1 1 0)) hU hdiag hoff
  have hc : 8 * G * G + 8 * G * G = 16 * G^2 := by ring
  simpa only [Matrix.det_fin_two, hc] using hdet

theorem metricAdjugate_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G) (i j : Fin 2) :
    CoordinateBound (fun p => (g p).adjugate i j) U 3 G := by
  fin_cases i <;> fin_cases j
  · simpa [Matrix.adjugate_fin_two] using hgB 1 1
  · simpa [Matrix.adjugate_fin_two] using CoordinateBound.neg (hg.1 0 1) hU (hgB 0 1)
  · simpa [Matrix.adjugate_fin_two] using CoordinateBound.neg (hg.1 1 0) hU (hgB 1 0)
  · simpa [Matrix.adjugate_fin_two] using hgB 0 0

theorem inverseMetric_eq_adjugate_div (g : MetricField) (i j : Fin 2) :
    (fun p => inverseMetric g p i j) = (fun p => (g p).adjugate i j / (g p).det) := by
  funext p
  simp [inverseMetric, Matrix.inv_def, Ring.inverse_eq_inv, div_eq_mul_inv, smul_eq_mul, mul_comm]

theorem inverseMetric_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) (i j : Fin 2) :
    CoordinateBound (fun p => inverseMetric g p i j) U 3 (metricInverseJetBound G d) := by
  have hN : 0 ≤ metricQuotientNumeratorBound G := by dsimp [metricQuotientNumeratorBound]; positivity
  have hGN : G ≤ metricQuotientNumeratorBound G := by dsimp [metricQuotientNumeratorBound]; nlinarith [sq_nonneg G]
  have hDN : 16 * G^2 ≤ metricQuotientNumeratorBound G := by dsimp [metricQuotientNumeratorBound]; linarith
  have hadj := (metricAdjugate_coordinate_bound hg hU hgB i j).mono le_rfl hGN
  have hdetB := (metricDet_coordinate_bound hg hU hG hgB).mono le_rfl hDN
  rw [inverseMetric_eq_adjugate_div]
  intro ds hds p hp
  exact LowQuotient.quotient_bound_through_three (metricAdjugate_contDiffOn hg i j)
    (metricDet_contDiffOn hg) hU hN hd hadj hdetB hdet ds hds hp

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Sobolev
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem boxPoint_eta (p : Coord) : boxPoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> simp [boxPoint]

end SmoothLocal.Sobolev

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

variable {A B C v u f : Coord → ℝ} {U : Set Coord} {p : Coord}

variable {tl tr sb st : ℝ}

theorem rectangleIntegral_mono {F G : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hG : ContinuousOn G (closedRectangle tl tr sb st))
    (hle : ∀ p ∈ closedRectangle tl tr sb st, F p ≤ G p) :
    rectangleIntegral tl tr sb st F ≤ rectangleIntegral tl tr sb st G := by
  rw [rectangleIntegral_eq_area ht hs hF, rectangleIntegral_eq_area ht hs hG]
  apply setIntegral_mono_on (rectangle_area_integrable hF) (rectangle_area_integrable hG)
    (measurableSet_Ioc.prod measurableSet_Ioc)
  intro p hp
  exact hle (boxPoint p.1 p.2) (boxPoint_mem
    (Ioc_subset_Icc_self hp.1) (Ioc_subset_Icc_self hp.2))

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem fderiv_axis_eq_deriv_update {n : ℕ} {f : (Fin n → ℝ) → ℝ} {w : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f w) (i : Fin n) :
    fderiv ℝ f w (Pi.single i 1) = deriv (fun t => f (Function.update w i t)) (w i) := by
  have hd : HasFDerivAt f (fderiv ℝ f w) (Function.update w i (w i)) := by
    simpa using hf.hasFDerivAt
  exact (hd.comp_hasDerivAt (w i) (hasDerivAt_update w i (w i))).deriv.symm

def gradientStateIndex (i : Fin 2) : Fin 6 := if i = 0 then 2 else 3

theorem sixVariableP_update_gradient (g : MetricField) (w : DarbouxState) (i : Fin 2) (t : ℝ) :
    sixVariableP g (Function.update w (gradientStateIndex i) t) =
      solvedDarboux g (statePoint w) (w 4) (w 5) (Function.update (stateGradient w) i t) := by
  have hp : statePoint (Function.update w (gradientStateIndex i) t) = statePoint w := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [gradientStateIndex, statePoint]
  have hv : stateGradient (Function.update w (gradientStateIndex i) t) =
      Function.update (stateGradient w) i t := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [gradientStateIndex, stateGradient]
  unfold sixVariableP
  rw [hp, hv]
  fin_cases i <;> simp [gradientStateIndex]

theorem sixVariableP_update_mixed (g : MetricField) (w : DarbouxState) (t : ℝ) :
    sixVariableP g (Function.update w 4 t) =
      solvedDarboux g (statePoint w) t (w 5) (stateGradient w) := by
  have hp : statePoint (Function.update w 4 t) = statePoint w := by
    ext j
    fin_cases j <;> simp [statePoint]
  have hv : stateGradient (Function.update w 4 t) = stateGradient w := by
    ext j
    fin_cases j <;> simp [stateGradient]
  unfold sixVariableP
  rw [hp, hv]
  simp

theorem sixVariableP_update_yy (g : MetricField) (w : DarbouxState) (t : ℝ) :
    sixVariableP g (Function.update w 5 t) =
      solvedDarboux g (statePoint w) (w 4) t (stateGradient w) := by
  have hp : statePoint (Function.update w 5 t) = statePoint w := by
    ext j
    fin_cases j <;> simp [statePoint]
  have hv : stateGradient (Function.update w 5 t) = stateGradient w := by
    ext j
    fin_cases j <;> simp [stateGradient]
  unfold sixVariableP
  rw [hp, hv]
  simp

theorem solvedDarboux_first_variables_differentiableAt (g : MetricField) (p u : Coord) (b c : ℝ)
    (hyy : jetYY g p c u ≠ 0) : DifferentiableAt ℝ (solvedDarboux g p b c) u := by
  have hd := (jetConnection_differentiableAt g p u 0 0).add
    ((jetNumerator_differentiableAt g p u b).mul ((jetYY_differentiableAt g p u c).inv hyy))
  exact hd

theorem sixVariableP_gradient_axis
    {g : MetricField} {U : Set Coord} {w : DarbouxState}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hw : w ∈ darbouxStateDomain g U) (i : Fin 2) :
    fderiv ℝ (sixVariableP g) w (Pi.single (gradientStateIndex i) 1) =
      coordPartial i (solvedDarboux g (statePoint w) (w 4) (w 5)) (stateGradient w) := by
  have hP : DifferentiableAt ℝ (sixVariableP g) w :=
    ((sixVariableP_contDiffOn hg hU).contDiffAt
      ((darbouxStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by simp)
  rw [fderiv_axis_eq_deriv_update hP]
  have heq : (fun t => sixVariableP g (Function.update w (gradientStateIndex i) t)) =
      (fun t => solvedDarboux g (statePoint w) (w 4) (w 5) (Function.update (stateGradient w) i t)) :=
    funext (sixVariableP_update_gradient g w i)
  rw [heq]
  have hi : w (gradientStateIndex i) = stateGradient w i := by
    fin_cases i <;> simp [gradientStateIndex, stateGradient]
  rw [hi]
  exact (fderiv_axis_eq_deriv_update
    (solvedDarboux_first_variables_differentiableAt g (statePoint w) (stateGradient w) (w 4) (w 5) hw.2) i).symm

theorem sixVariableP_gradient_axis_at_height
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single (gradientStateIndex i) 1) =
      heightPFirst g z i p := by
  rw [sixVariableP_gradient_axis hg hU (solutionJet_mem_domain g z hp hyy) i,
    statePoint_solutionJet, stateGradient_solutionJet]
  rfl

theorem sixVariableP_mixed_axis_at_height
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 4 1) = 2 * hessianQuotient g z p := by
  have hP := (sixVariableP_contDiffAt_solutionJet hg hU hp hyy).differentiableAt (by simp)
  rw [fderiv_axis_eq_deriv_update hP]
  have heq : (fun t => sixVariableP g (Function.update (solutionJet z p) 4 t)) =
      (fun t => solvedDarboux g p t (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p)) := by
    funext t
    rw [sixVariableP_update_mixed, statePoint_solutionJet, stateGradient_solutionJet]
    rfl
  rw [heq]
  change deriv (fun t => solvedDarboux g p t (coordPartial 1 (coordPartial 1 z) p)
    (fun i => coordPartial i z p)) (coordPartial 0 (coordPartial 1 z) p) = _
  rw [solvedDarboux_deriv_b g p _ _ _ hyy, jetMixed_at_height, jetYY_at_height]
  rfl

theorem sixVariableP_yy_axis_at_height
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 5 1) =
      -((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) := by
  have hP := (sixVariableP_contDiffAt_solutionJet hg hU hp hyy).differentiableAt (by simp)
  rw [fderiv_axis_eq_deriv_update hP]
  have heq : (fun t => sixVariableP g (Function.update (solutionJet z p) 5 t)) =
      (fun t => solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p) t (fun i => coordPartial i z p)) := by
    funext t
    rw [sixVariableP_update_yy, statePoint_solutionJet, stateGradient_solutionJet]
    rfl
  rw [heq]
  change deriv (fun t => solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p) t
    (fun i => coordPartial i z p)) (coordPartial 1 (coordPartial 1 z) p) = _
  rw [solvedDarboux_deriv_c g p _ _ _ hyy, jetMixed_at_height, jetYY_at_height,
    jetEnergy_at_height hg hp z]
  unfold hessianQuotient darbouxG
  ring

theorem sixVariableP_vertical_direction
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (v : DarbouxState) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) v =
      heightPFirst g z 0 p * v 2 + heightPFirst g z 1 p * v 3 +
        2 * hessianQuotient g z p * v 4 -
        ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) * v 5 := by
  have he : v = v 2 • (Pi.single 2 (1 : ℝ) : DarbouxState) +
      v 3 • Pi.single 3 1 + v 4 • Pi.single 4 1 + v 5 • Pi.single 5 1 := by
    ext i
    fin_cases i <;> simp [hv0, hv1]
  have h0 : fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 2 1) = heightPFirst g z 0 p := by
    simpa only [gradientStateIndex, ↓reduceIte] using sixVariableP_gradient_axis_at_height hg hU hp hyy 0
  have h1 : fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 3 1) = heightPFirst g z 1 p := by
    simpa only [gradientStateIndex, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] using
      sixVariableP_gradient_axis_at_height hg hU hp hyy 1
  have hl := congrArg (fderiv ℝ (sixVariableP g) (solutionJet z p)) he
  simp only [map_add, map_smul, h0, h1, sixVariableP_mixed_axis_at_height hg hU hp hyy,
    sixVariableP_yy_axis_at_height hg hU hp hyy, smul_eq_mul] at hl
  rw [hl]
  ring

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation

def ChainWord.single (n : ℕ) : ChainWord := ⟨1, ![n]⟩

def chainSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (ws : List ChainWord) (t : ℝ) : ℝ :=
  (ws.map (fun w => chainTerm F J w t)).sum

theorem chainSum_append
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (ws vs : List ChainWord) (t : ℝ) :
    chainSum F J (ws ++ vs) t = chainSum F J ws t + chainSum F J vs t := by
  simp [chainSum]

theorem chainSum_replicate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (w : ChainWord) (n : ℕ) (t : ℝ) :
    chainSum F J (List.replicate n w) t = (n : ℝ) * chainTerm F J w t := by
  simp [chainSum, nsmul_eq_mul]

theorem chainSum_children
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (w : ChainWord) (t : ℝ) :
    chainSum F J w.children t = chainTerm F J w.prepend t +
      ∑ i, chainTerm F J (w.bump i) t := by
  simp [chainSum, ChainWord.children, List.map_ofFn, List.sum_ofFn]

theorem chainSum_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t)
    (ws : List ChainWord) :
    HasDerivAt (chainSum F J ws) (chainSum F J (ws.flatMap ChainWord.children) t) t := by
  induction ws with
  | nil => convert hasDerivAt_const t (0 : ℝ) using 1 <;> rfl
  | cons w ws ih =>
    have hw := chainTerm_hasDerivAt hF hJ w
    rw [← chainSum_children] at hw
    convert hw.add ih using 1 <;> try rfl
    rw [List.flatMap_cons, chainSum_append]

theorem topResidualWords_sum_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (m : ℕ) (t : ℝ) :
    chainSum F J (topResidualWords (m + 1)) t =
      chainSum F J ((topResidualWords m).flatMap ChainWord.children) t +
      (m + 3 : ℝ) * chainTerm F J (ChainWord.triple 1 1 (m + 2)) t +
      (m + 3 : ℝ) * chainTerm F J (ChainWord.pair 2 (m + 2)) t := by
  simp only [topResidualWords, chainSum_append, chainSum_replicate, Nat.cast_add,
    Nat.cast_ofNat, add_assoc]

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Metric Function
open scoped Topology NNReal ContDiff

namespace SmoothLocal.Flow

theorem exists_confined_continuous_picard_family
    {f : ℝ → ℝ → ℝ} {tmin tmax : ℝ} {t0 : Icc tmin tmax} {x0 : ℝ}
    {a r L K : ℝ≥0} (hf : IsPicardLindelof f t0 x0 a r L K) :
    ∃ Y : ℝ → ℝ → ℝ,
      (∀ s ∈ closedBall x0 r, Y s t0 = s ∧
        ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (Y s) (f t (Y s t)) (Icc tmin tmax) t) ∧
      (∀ s ∈ closedBall x0 r, ∀ t, Y s t ∈ closedBall x0 a) ∧
      (∃ J : ℝ≥0, ∀ t, LipschitzOnWith J (fun s => Y s t) (closedBall x0 r)) ∧
      ContinuousOn (uncurry Y) (closedBall x0 r ×ˢ Icc tmin tmax) ∧
      (∀ s ∈ closedBall x0 r, LipschitzOnWith L (Y s) (Icc tmin tmax)) := by
  classical
  have hex (s : ℝ) (hs : s ∈ closedBall x0 r) :=
    ODE.FunSpace.exists_isFixedPt_next hf hs
  choose alpha halpha using hex
  let Y : ℝ → ℝ → ℝ := fun s => if hs : s ∈ closedBall x0 r then
    (alpha s hs).compProj else fun _ => 0
  have hY (s : ℝ) (hs : s ∈ closedBall x0 r) : Y s = (alpha s hs).compProj := by
    simp only [Y, dite_eq_left hs]
  have hstart (s : ℝ) (hs : s ∈ closedBall x0 r) : Y s t0 = s := by
    rw [hY s hs, ODE.FunSpace.compProj_val, ← halpha s hs,
      ODE.FunSpace.next_apply₀]
  have hderiv (s : ℝ) (hs : s ∈ closedBall x0 r) (t : ℝ)
      (ht : t ∈ Icc tmin tmax) :
      HasDerivWithinAt (Y s) (f t (Y s t)) (Icc tmin tmax) t := by
    rw [hY s hs]
    apply ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
      (alpha s hs).continuous_compProj.continuousOn
      (fun _ _ => (alpha s hs).compProj_mem_closedBall hf.mul_max_le) s ht
      |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← halpha s hs]
    rw [ODE.FunSpace.compProj_of_mem ht']
    exact ODE.FunSpace.next_apply hf hs (alpha s hs)
  have hrange (s : ℝ) (hs : s ∈ closedBall x0 r) (t : ℝ) :
      Y s t ∈ closedBall x0 a := by
    rw [hY s hs]
    exact (alpha s hs).compProj_mem_closedBall hf.mul_max_le
  obtain ⟨J, hJ⟩ := ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
  have hinitLip (t : ℝ) : LipschitzOnWith J (fun s => Y s t) (closedBall x0 r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs u hu
    rw [hY s hs, hY u hu, ODE.FunSpace.compProj_apply, ODE.FunSpace.compProj_apply,
      ← ODE.FunSpace.toContinuousMap_apply_eq_apply,
      ← ODE.FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t0⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact hJ s u hs hu (alpha s hs) (alpha u hu) (halpha s hs) (halpha u hu)
  have hcont : ContinuousOn (uncurry Y) (closedBall x0 r ×ˢ Icc tmin tmax) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ J
    · intro s hs
      exact HasDerivWithinAt.continuousOn (hderiv s hs)
    · intro t _
      exact hinitLip t
  have htimeLip (s : ℝ) (hs : s ∈ closedBall x0 r) :
      LipschitzOnWith L (Y s) (Icc tmin tmax) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht u hu
    rw [hY s hs, ODE.FunSpace.compProj_of_mem ht, ODE.FunSpace.compProj_of_mem hu]
    exact (alpha s hs).lipschitzWith.dist_le_mul ⟨t, ht⟩ ⟨u, hu⟩
  exact ⟨Y, fun s hs => ⟨hstart s hs, hderiv s hs⟩, hrange, ⟨J, hinitLip⟩, hcont, htimeLip⟩

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.Geometry

def connectionBracket (g : MetricField) (i j l : Fin 2) (p : Coord) : ℝ :=
  coordPartial i (fun x => g x j l) p + coordPartial j (fun x => g x i l) p -
    coordPartial l (fun x => g x i j) p

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}

theorem connectionBracket_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (i j l : Fin 2) : ContDiffOn ℝ ∞ (connectionBracket g i j l) U :=
  ((partial_contDiffOn (hg.1 j l) hU i).add
    (partial_contDiffOn (hg.1 i l) hU j)).sub (partial_contDiffOn (hg.1 i j) hU l)

theorem connectionBracket_coordinate_bound (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G) (i j l : Fin 2) :
    CoordinateBound (connectionBracket g i j l) U 3 (3 * G) := by
  have h1 : CoordinateBound (coordPartial i (fun p => g p j l)) U 3 G := (hgB j l).partial_bound i
  have h2 : CoordinateBound (coordPartial j (fun p => g p i l)) U 3 G := (hgB i l).partial_bound j
  have h3 : CoordinateBound (coordPartial l (fun p => g p i j)) U 3 G := (hgB i j).partial_bound l
  have hb := CoordinateBound.sub
    ((partial_contDiffOn (hg.1 j l) hU i).add (partial_contDiffOn (hg.1 i l) hU j))
    (partial_contDiffOn (hg.1 i j) hU l) hU
    (CoordinateBound.add (partial_contDiffOn (hg.1 j l) hU i)
      (partial_contDiffOn (hg.1 i l) hU j) hU h1 h2) h3
  have he : G + G + G = 3 * G := by ring
  rw [he] at hb
  exact hb

theorem christoffel_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) (k i j : Fin 2) :
    CoordinateBound (christoffel g k i j) U 3 (christoffelJetBound G d) := by
  have hg3 (a b : Fin 2) : CoordinateBound (fun p => g p a b) U 3 G :=
    (hgB a b).mono (by norm_num) le_rfl
  have hI := metricInverseJetBound_nonneg hG hd
  have hprod (l : Fin 2) : CoordinateBound
      (fun p => inverseMetric g p k l * connectionBracket g i j l p) U 3
      (8 * metricInverseJetBound G d * (3 * G)) :=
    CoordinateBound.mul_through_three (inverseMetric_contDiffOn hg k l)
      (connectionBracket_contDiffOn hg hU i j l) hU hI (by positivity)
      (inverseMetric_coordinate_bound hg hU hG hd hg3 hdet k l)
      (connectionBracket_coordinate_bound hg hU hgB i j l)
  have hs := CoordinateBound.add
    ((inverseMetric_contDiffOn hg k 0).mul (connectionBracket_contDiffOn hg hU i j 0))
    ((inverseMetric_contDiffOn hg k 1).mul (connectionBracket_contDiffOn hg hU i j 1))
    hU (hprod 0) (hprod 1)
  have hhalf := CoordinateBound.const_mul
    (((inverseMetric_contDiffOn hg k 0).mul (connectionBracket_contDiffOn hg hU i j 0)).add
      ((inverseMetric_contDiffOn hg k 1).mul (connectionBracket_contDiffOn hg hU i j 1)))
    hU hs (1 / 2 : ℝ)
  have hc : |(1 / 2 : ℝ)| *
      (8 * metricInverseJetBound G d * (3 * G) + 8 * metricInverseJetBound G d * (3 * G)) =
      christoffelJetBound G d := by
    norm_num [christoffelJetBound]
    ring
  rw [hc] at hhalf
  convert hhalf using 1
  funext p
  simp only [christoffel, Fin.sum_univ_two, connectionBracket]

theorem covHessian_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) (i j : Fin 2) :
    CoordinateBound (fun p => covHessian g z p i j) U 3 (hessianJetBound G Z d) := by
  have hz4 (a : Fin 2) : CoordinateBound (coordPartial a z) U 4 Z := hzB.partial_bound a
  have hz1 (a : Fin 2) : CoordinateBound (coordPartial a z) U 3 Z :=
    (hz4 a).mono (by norm_num) le_rfl
  have hz2 : CoordinateBound (coordPartial i (coordPartial j z)) U 3 Z := (hz4 j).partial_bound i
  have hΓ := christoffelJetBound_nonneg hG hd
  have hprod (a : Fin 2) : CoordinateBound
      (fun p => christoffel g a i j p * coordPartial a z p) U 3
      (8 * christoffelJetBound G d * Z) :=
    CoordinateBound.mul_through_three (christoffel_contDiffOn hg hU a i j)
      (partial_contDiffOn hz hU a) hU hΓ hZ
      (christoffel_coordinate_bound hg hU hG hd hgB hdet a i j) (hz1 a)
  have hs := CoordinateBound.add
    ((christoffel_contDiffOn hg hU 0 i j).mul (partial_contDiffOn hz hU 0))
    ((christoffel_contDiffOn hg hU 1 i j).mul (partial_contDiffOn hz hU 1))
    hU (hprod 0) (hprod 1)
  have hh := CoordinateBound.sub (partial_contDiffOn (partial_contDiffOn hz hU j) hU i)
    (((christoffel_contDiffOn hg hU 0 i j).mul (partial_contDiffOn hz hU 0)).add
      ((christoffel_contDiffOn hg hU 1 i j).mul (partial_contDiffOn hz hU 1))) hU hz2 hs
  have hc : Z + (8 * christoffelJetBound G d * Z + 8 * christoffelJetBound G d * Z) =
      hessianJetBound G Z d := by dsimp [hessianJetBound]; ring
  simpa only [covHessian, Fin.sum_univ_two, hc] using hh

theorem hessianQuotient_bound_from_metric_height_jets
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) :
    ContDiffOn ℝ ∞ (hessianQuotient g z) U ∧
      CoordinateBound (hessianQuotient g z) U 3
        (LowQuotient.boundThroughThree (hessianJetBound G Z d) c) := by
  exact hessianQuotient_coordinate_bound_through_three hg hU hz
    (hessianJetBound_nonneg hG hZ hd) hc
    (fun i j => covHessian_coordinate_bound hg hU hz hG hZ hd hgB hzB hdet i j) hyy

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation

theorem ChainWord.prepend_single (n : ℕ) :
    (ChainWord.single n).prepend = ChainWord.pair 1 n := rfl

theorem ChainWord.bump_single (n : ℕ) :
    (ChainWord.single n).bump (0 : Fin 1) = ChainWord.single (n + 1) := by
  change ChainWord.mk 1 _ = ChainWord.mk 1 _
  congr 1
  ext i
  fin_cases i
  simp [ChainWord.single]

theorem ChainWord.prepend_pair (a b : ℕ) :
    (ChainWord.pair a b).prepend = ChainWord.triple 1 a b := rfl

theorem ChainWord.bump_pair_zero (a b : ℕ) :
    (ChainWord.pair a b).bump (0 : Fin 2) = ChainWord.pair (a + 1) b := by
  apply congrArg (ChainWord.mk 2)
  change Function.update (![a, b] : Fin 2 → ℕ) (0 : Fin 2) (a + 1) = ![a + 1, b]
  funext i
  fin_cases i <;> simp

theorem ChainWord.bump_pair_one (a b : ℕ) :
    (ChainWord.pair a b).bump (1 : Fin 2) = ChainWord.pair a (b + 1) := by
  change ChainWord.mk 2 _ = ChainWord.mk 2 _
  congr 1
  ext i
  fin_cases i <;> simp [ChainWord.pair]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem chainTerm_single_eq (F : E → ℝ) (J : ℝ → E) (n : ℕ) (t : ℝ) :
    chainTerm F J (ChainWord.single n) t =
      fderiv ℝ F (J t) (iteratedDeriv n J t) := by
  simp only [chainTerm, ChainWord.single, Matrix.cons_val_fin_one]
  exact iteratedFDeriv_one_apply (𝕜 := ℝ) (f := F) (x := J t)
    (fun _ : Fin 1 => iteratedDeriv n J t)

theorem chainTerm_pair_eq (F : E → ℝ) (J : ℝ → E) (a b : ℕ) (t : ℝ) :
    chainTerm F J (ChainWord.pair a b) t =
      iteratedFDeriv ℝ 2 F (J t) ![iteratedDeriv a J t, iteratedDeriv b J t] := by
  apply congrArg (iteratedFDeriv ℝ 2 F (J t))
  ext i
  fin_cases i <;> rfl

theorem chainTerm_triple_eq (F : E → ℝ) (J : ℝ → E) (a b c : ℕ) (t : ℝ) :
    chainTerm F J (ChainWord.triple a b c) t =
      iteratedFDeriv ℝ 3 F (J t)
        ![iteratedDeriv a J t, iteratedDeriv b J t, iteratedDeriv c J t] := by
  apply congrArg (iteratedFDeriv ℝ 3 F (J t))
  ext i
  fin_cases i <;> rfl

theorem chainTerm_pair_symm {F : E → ℝ} (J : ℝ → E) {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (a b : ℕ) :
    chainTerm F J (ChainWord.pair a b) t = chainTerm F J (ChainWord.pair b a) t := by
  rw [chainTerm_pair_eq, chainTerm_pair_eq]
  have hs := hF.isSymmSndFDerivAt (by
    simp only [minSmoothness, ite_eq_left (inferInstance : IsRCLikeNormedField ℝ)]
    exact WithTop.coe_le_coe.mpr le_top)
  exact hs.iteratedFDeriv_cons

theorem chainTerm_single_hasDerivAt {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t) (n : ℕ) :
    HasDerivAt (chainTerm F J (ChainWord.single n))
      (chainTerm F J (ChainWord.single (n + 1)) t +
        chainTerm F J (ChainWord.pair 1 n) t) t := by
  have h := chainTerm_hasDerivAt hF hJ (ChainWord.single n)
  change HasDerivAt _
    (chainTerm F J (ChainWord.single n).prepend t +
      ∑ i : Fin 1, chainTerm F J ((ChainWord.single n).bump i) t) t at h
  simpa only [Fin.sum_univ_one, ChainWord.prepend_single, ChainWord.bump_single,
    add_comm] using h

theorem chainTerm_pair_hasDerivAt {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t) (a b : ℕ) :
    HasDerivAt (chainTerm F J (ChainWord.pair a b))
      (chainTerm F J (ChainWord.triple 1 a b) t +
        chainTerm F J (ChainWord.pair (a + 1) b) t +
        chainTerm F J (ChainWord.pair a (b + 1)) t) t := by
  have h := chainTerm_hasDerivAt hF hJ (ChainWord.pair a b)
  change HasDerivAt _
    (chainTerm F J (ChainWord.pair a b).prepend t +
      ∑ i : Fin 2, chainTerm F J ((ChainWord.pair a b).bump i) t) t at h
  simpa only [Fin.sum_univ_two, ChainWord.prepend_pair, ChainWord.bump_pair_zero,
    ChainWord.bump_pair_one, add_assoc] using h

theorem top_chain_three {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t) :
    iteratedDeriv 3 (F ∘ J) t =
      chainTerm F J (ChainWord.single 3) t +
        3 * chainTerm F J (ChainWord.pair 1 2) t +
        chainSum F J (topResidualWords 0) t := by
  have h := iteratedDeriv_vcomp_three
    (hF.of_le (WithTop.coe_le_coe.mpr le_top))
    (hJ.of_le (WithTop.coe_le_coe.mpr le_top))
  have heq : iteratedDeriv 3 (F ∘ J) t =
      chainTerm F J (ChainWord.triple 1 1 1) t +
      chainTerm F J (ChainWord.pair 2 1) t +
      2 * chainTerm F J (ChainWord.pair 1 2) t +
      chainTerm F J (ChainWord.single 3) t := by
    rw [chainTerm_triple_eq, chainTerm_pair_eq, chainTerm_pair_eq, chainTerm_single_eq]
    simp only [iteratedDeriv_one, two_smul, two_mul] at h ⊢
    convert h using 1
    have hv : (![deriv J t, deriv J t, deriv J t] : Fin 3 → E) = fun _ => deriv J t := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
  rw [chainTerm_pair_symm J hF 2 1] at heq
  simp only [topResidualWords, chainSum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  linarith [heq]

theorem top_chain_expansion
    {F : E → ℝ} {J : ℝ → E} {O : Set E} {I : Set ℝ}
    (hO : IsOpen O) (hI : IsOpen I) (hF : ContDiffOn ℝ ∞ F O)
    (hJ : ContDiffOn ℝ ∞ J I) (hmap : MapsTo J I O) :
    ∀ m t, t ∈ I →
      iteratedDeriv (m + 3) (F ∘ J) t =
        chainTerm F J (ChainWord.single (m + 3)) t +
          (m + 3 : ℝ) * chainTerm F J (ChainWord.pair 1 (m + 2)) t +
          chainSum F J (topResidualWords m) t := by
  intro m
  induction m with
  | zero =>
    intro t ht
    simpa only [Nat.zero_add, Nat.cast_zero, zero_add] using top_chain_three (hF.contDiffAt (hO.mem_nhds (hmap ht)))
      (hJ.contDiffAt (hI.mem_nhds ht))
  | succ m ih =>
    intro t ht
    have hFt := hF.contDiffAt (hO.mem_nhds (hmap ht))
    have hJt := hJ.contDiffAt (hI.mem_nhds ht)
    have heq : iteratedDeriv (m + 3) (F ∘ J) =ᶠ[𝓝 t]
        (fun r => chainTerm F J (ChainWord.single (m + 3)) r +
          (m + 3 : ℝ) * chainTerm F J (ChainWord.pair 1 (m + 2)) r +
          chainSum F J (topResidualWords m) r) := by
      filter_upwards [hI.mem_nhds ht] with r hr
      exact ih r hr
    have hd := ((chainTerm_single_hasDerivAt hFt hJt (m + 3)).add
      ((chainTerm_pair_hasDerivAt hFt hJt 1 (m + 2)).const_mul (m + 3 : ℝ))).add
      (chainSum_hasDerivAt hFt hJt (topResidualWords m))
    have hd' := hd.deriv
    change deriv (fun r => chainTerm F J (ChainWord.single (m + 3)) r +
      (m + 3 : ℝ) * chainTerm F J (ChainWord.pair 1 (m + 2)) r +
      chainSum F J (topResidualWords m) r) t = _ at hd'
    rw [show m + 1 + 3 = (m + 3) + 1 by omega, iteratedDeriv_succ, heq.deriv_eq, hd']
    rw [topResidualWords_sum_succ]
    simp only [Nat.cast_add, Nat.add_assoc, Nat.reduceAdd]
    ring

theorem actualP_top_chain_expansion
    {g : SmoothLocal.Geometry.MetricField} {z : SmoothLocal.Geometry.Coord → ℝ}
    {U : Set SmoothLocal.Geometry.Coord} {x y : ℝ}
    (hg : SmoothLocal.Geometry.SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, SmoothLocal.Geometry.covHessian g z p 1 1 ≠ 0)
    (hp : (![x, y] : SmoothLocal.Geometry.Coord) ∈ U) (m : ℕ) :
    iteratedDeriv (m + 3) (sixVariableP g ∘ solutionJetCurve z x) y =
      chainTerm (sixVariableP g) (solutionJetCurve z x) (ChainWord.single (m + 3)) y +
      (m + 3 : ℝ) * chainTerm (sixVariableP g) (solutionJetCurve z x)
        (ChainWord.pair 1 (m + 2)) y +
      chainSum (sixVariableP g) (solutionJetCurve z x) (topResidualWords m) y := by
  let I : Set ℝ := {t | (![x, t] : SmoothLocal.Geometry.Coord) ∈ U}
  have hI : IsOpen I := hU.preimage (verticalPoint_contDiff x).continuous
  have hJ : ContDiffOn ℝ ∞ (solutionJetCurve z x) I := by
    intro t ht
    exact (solutionJetCurve_contDiffAt hU hz ht).contDiffWithinAt
  have hmap : MapsTo (solutionJetCurve z x) I (darbouxStateDomain g U) := by
    intro t ht
    exact solutionJet_mem_domain g z ht (hyy _ ht)
  exact top_chain_expansion (darbouxStateDomain_isOpen hg hU) hI
    (sixVariableP_contDiffOn hg hU) hJ hmap m y hp

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function
open scoped ContDiff BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def fullBlockPartition (ell : ℕ) (hell : 0 < ell) : OrderedFinpartition ell where
  length := 1
  partSize _ := ell
  partSize_pos _ := hell
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := by
    intro firstBlock _ secondBlock _ hne
    exact (hne (Subsingleton.elim firstBlock secondBlock)).elim
  cover i := ⟨0, i, rfl⟩

def darbouxFaaTerm (g : MetricField) (z : Coord → ℝ) (x y : ℝ)
    {ell : ℕ} (c : OrderedFinpartition ell) : ℝ :=
  iteratedFDeriv ℝ c.length (sixVariableP g) (solutionJetCurve z x y)
    (fun j => iteratedDeriv (c.partSize j) (solutionJetCurve z x) y)

def directLinearization (g : MetricField) (z u : Coord → ℝ) (p : Coord) : ℝ :=
  heightPFirst g z 0 p * coordPartial 0 u p + heightPFirst g z 1 p * coordPartial 1 u p +
    2 * hessianQuotient g z p * coordPartial 0 (coordPartial 1 u) p -
    ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) *
      coordPartial 1 (coordPartial 1 u) p

theorem fullBlockPartition_term (g : MetricField) (z : Coord → ℝ) (x y : ℝ)
    (ell : ℕ) (hell : 0 < ell) :
    darbouxFaaTerm g z x y (fullBlockPartition ell hell) =
      fderiv ℝ (sixVariableP g) (solutionJetCurve z x y)
        (iteratedDeriv ell (solutionJetCurve z x) y) := by
  exact iteratedFDeriv_one_apply (𝕜 := ℝ) (f := sixVariableP g)
    (x := solutionJetCurve z x y) (fun _ : Fin 1 => iteratedDeriv ell (solutionJetCurve z x) y)

theorem fullBlockPartition_actual_linearization
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : (![x, y] : Coord) ∈ U) (hyy : covHessian g z ![x, y] 1 1 ≠ 0)
    (ell : ℕ) (hell : 2 ≤ ell) :
    darbouxFaaTerm g z x y (fullBlockPartition ell (by omega)) =
      directLinearization g z (verticalJet z ell) ![x, y] := by
  rw [fullBlockPartition_term, solutionJetCurve_iteratedDeriv hU hz hp ell hell]
  change fderiv ℝ (sixVariableP g) (solutionJet z ![x, y]) _ = _
  rw [sixVariableP_vertical_direction hg hU hp hyy _ (by rfl) (by rfl)]
  rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem exists_cap_flow {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100) :
    ∃ Y : ℝ → ℝ → ℝ,
      ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ContDiffOn ℝ ∞ (Y s) (Icc (-2 : ℝ) 2)) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        |Y s t - s| ≤ (1 : ℝ) / 100 * |t|) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, |Y s t - s| ≤ (1 : ℝ) / 50) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        |Y s t| ≤ (101 : ℝ) / 50 ∧ coordinatePoint t (Y s t) ∈ modelSquare) ∧
      (∃ J : ℝ≥0, ∀ t, LipschitzOnWith J (fun s => Y s t) (Icc (-2 : ℝ) 2)) := by
  obtain ⟨L, hPL⟩ := exists_cap_picard hq hU hSU hsmall
  obtain ⟨Y, hY, hconf, ⟨J, hJ⟩, hcont, htime⟩ :=
    exists_confined_continuous_picard_family hPL
  have hball (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) :
      s ∈ closedBall (0 : ℝ) (↑(2 : ℝ≥0)) := by
    simpa only [mem_closedBall, Real.dist_eq, sub_zero, NNReal.coe_ofNat] using abs_le.mpr hs
  have hz : (0 : ℝ) ∈ Icc (-2 : ℝ) 2 := by norm_num
  have hstart (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) : Y s 0 = s :=
    (hY s (hball s hs)).1
  have hderiv (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) (t : ℝ)
      (ht : t ∈ Icc (-2 : ℝ) 2) :
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t :=
    (hY s (hball s hs)).2 t ht
  have hdispl (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) (t : ℝ)
      (ht : t ∈ Icc (-2 : ℝ) 2) : |Y s t - s| ≤ (1 : ℝ) / 100 * |t| := by
    have hh := (htime s (hball s hs)).dist_le_mul t ht 0 hz
    rw [hstart s hs] at hh
    simpa only [Real.dist_eq, sub_zero, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh
  have hdispl' (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) (t : ℝ)
      (ht : t ∈ Icc (-2 : ℝ) 2) : |Y s t - s| ≤ (1 : ℝ) / 50 := by
    have hd := hdispl s hs t ht
    have habs := abs_le.mpr ht
    nlinarith
  have hfield : ContDiffOn ℝ ∞ (uncurry (flowField q))
      (Icc (-2 : ℝ) 2 ×ˢ closedBall (0 : ℝ) 3) := by
    apply hq.neg.comp (by unfold coordinatePoint; fun_prop)
    intro p hp
    have hy : |p.2| ≤ 3 := by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hp.2
    exact hSU (coordinatePoint_mem_modelSquare
      ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩ (abs_le.mp hy))
  refine ⟨Y, hcont.mono (fun p hp => ⟨hball p.1 hp.1, hp.2⟩), ?_, hstart,
    hderiv, hdispl, hdispl', ?_, ⟨J, fun t => (hJ t).mono (fun s hs => hball s hs)⟩⟩
  · intro s hs
    exact ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt hfield (hderiv s hs)
      (fun t _ => hconf s (hball s hs) t)
  · intro s hs t ht
    have hys : |Y s t| ≤ (101 : ℝ) / 50 := by
      have hsum : |Y s t| ≤ |Y s t - s| + |s| := by
        simpa only [sub_add_cancel] using abs_add_le (Y s t - s) s
      have hd := hdispl' s hs t ht
      have hs2 := abs_le.mpr hs
      linarith
    refine ⟨hys, coordinatePoint_mem_modelSquare
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ ?_⟩
    exact abs_le.mp (hys.trans (by norm_num))

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Metric Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def verticalAverageDerivative (q : Coord → ℝ) (t y0 y1 : ℝ) : ℝ :=
  ∫ u in 0..1, coordPartial 1 q (coordinatePoint t (y0 + u * (y1 - y0)))

theorem verticalSegment_mem_modelSquare {t y0 y1 u : ℝ}
    (ht : t ∈ Icc (-2 : ℝ) 2) (hy0 : y0 ∈ Icc (-3 : ℝ) 3)
    (hy1 : y1 ∈ Icc (-3 : ℝ) 3) (hu : u ∈ Icc (0 : ℝ) 1) :
    coordinatePoint t (y0 + u * (y1 - y0)) ∈ modelSquare := by
  apply coordinatePoint_mem_modelSquare
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hc := (convex_Icc (-3 : ℝ) 3) hy0 hy1
    (show 0 ≤ 1 - u by linarith [hu.2]) hu.1 (show (1 - u) + u = 1 by ring)
  have he : y0 + u * (y1 - y0) = (1 - u) * y0 + u * y1 := by ring
  rw [he]
  exact hc

theorem vertical_secant_identity {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {t y0 y1 : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2)
    (hy0 : y0 ∈ Icc (-3 : ℝ) 3) (hy1 : y1 ∈ Icc (-3 : ℝ) 3) :
    q (coordinatePoint t y1) - q (coordinatePoint t y0) =
      (y1 - y0) * verticalAverageDerivative q t y0 y1 := by
  let z (u : ℝ) := y0 + u * (y1 - y0)
  have hm (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : coordinatePoint t (z u) ∈ U :=
    hSU (verticalSegment_mem_modelSquare ht hy0 hy1 hu)
  have hc : ContinuousOn (fun u => coordPartial 1 q (coordinatePoint t (z u)))
      (Icc (0 : ℝ) 1) :=
    (partial_contDiffOn hq hU 1).continuousOn.comp
      (by unfold coordinatePoint z; fun_prop) hm
  have hd (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun v => q (coordinatePoint t (z v)))
        (coordPartial 1 q (coordinatePoint t (z u)) * (y1 - y0)) u := by
    have hu' : u ∈ Icc (0 : ℝ) 1 := by simpa using hu
    have hqy := ((hq.contDiffAt (hU.mem_nhds (hm u hu'))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt (z u) (coordinatePoint_hasDerivAt_y t (z u))
    have hz : HasDerivAt z (y1 - y0) u := by
      convert ((hasDerivAt_id u).mul_const (y1 - y0)).const_add y0 using 1 <;>
        first | rfl | ring
    convert hqy.comp u hz using 1 <;> rfl
  have hi : IntervalIntegrable
      (fun u => coordPartial 1 q (coordinatePoint t (z u))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using hc
  have hint : IntervalIntegrable
      (fun u => coordPartial 1 q (coordinatePoint t (z u)) * (y1 - y0)) volume 0 1 :=
    hi.mul_const (y1 - y0)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_mul_const] at hFTC
  have h0 : z 0 = y0 := by dsimp [z]; ring
  have h1 : z 1 = y1 := by dsimp [z]; ring
  rw [h0, h1] at hFTC
  unfold verticalAverageDerivative
  simpa only [z, mul_comm] using hFTC.symm

theorem verticalAverageDerivative_diagonal (q : Coord → ℝ) (t y : ℝ) :
    verticalAverageDerivative q t y y = coordPartial 1 q (coordinatePoint t y) := by
  simp [verticalAverageDerivative]

theorem flow_difference_hasDerivWithinAt {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {y0 y1 : ℝ → ℝ} {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2)
    (hy0 : y0 t ∈ Icc (-3 : ℝ) 3) (hy1 : y1 t ∈ Icc (-3 : ℝ) 3)
    (hdy0 : HasDerivWithinAt y0 (-q (coordinatePoint t (y0 t))) (Icc (-2 : ℝ) 2) t)
    (hdy1 : HasDerivWithinAt y1 (-q (coordinatePoint t (y1 t))) (Icc (-2 : ℝ) 2) t) :
    HasDerivWithinAt (fun v => y1 v - y0 v)
      (-verticalAverageDerivative q t (y0 t) (y1 t) * (y1 t - y0 t))
      (Icc (-2 : ℝ) 2) t := by
  have he := vertical_secant_identity hq hU hSU ht hy0 hy1
  convert hdy1.sub hdy0 using 1 <;> try with_reducible_and_instances rfl
  first | rfl | nlinarith only [he]

theorem scalar_linear_evolution_formula {a z : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (ha : ContinuousOn a (Ioo (-R) R))
    (hz : ∀ t ∈ Ioo (-R) R, HasDerivAt z (-a t * z t) t)
    {t : ℝ} (ht : t ∈ Ioo (-R) R) :
    z t = z 0 * Real.exp (-(∫ r in 0..t, a r)) := by
  let I (v : ℝ) := ∫ r in 0..v, a r
  have hzero : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
  have hI (v : ℝ) (hv : v ∈ Ioo (-R) R) : HasDerivAt I (a v) v := by
    have hseg : uIcc 0 v ⊆ Ioo (-R) R := by
      intro w hw
      exact ⟨(lt_min hzero.1 hv.1).trans_le hw.1,
        hw.2.trans_lt (max_lt hzero.2 hv.2)⟩
    exact intervalIntegral.integral_hasDerivAt_right (ha.mono hseg).intervalIntegrable
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo ha v hv)
      (ha.continuousAt (isOpen_Ioo.mem_nhds hv))
  have hprod (v : ℝ) (hv : v ∈ Ioo (-R) R) :
      HasDerivAt (fun w => z w * Real.exp (I w)) 0 v := by
    convert (hz v hv).mul ((hI v hv).exp) using 1 <;> try with_reducible_and_instances rfl
    first | rfl | ring
  have heq : z t * Real.exp (I t) = z 0 := by
    have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-R) R).isPreconnected
      (fun v hv => (hprod v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hprod v hv).deriv) ht hzero
    simpa [I] using hconst
  have he : Real.exp (I t) * Real.exp (-I t) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    z t = (z t * Real.exp (I t)) * Real.exp (-I t) := by rw [mul_assoc, he, mul_one]
    _ = z 0 * Real.exp (-I t) := by rw [heq]
    _ = _ := rfl

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

variable {tl tr sb st : ℝ} {S : Set Coord} {F G : Coord → ℝ}

theorem coordinateRectangle_closed_area_integrable
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    IntegrableOn (fun q : ℝ × ℝ => F (boxPoint q.1 q.2)) (Icc tl tr ×ˢ Icc sb st) := by
  have hc : ContinuousOn (fun q : ℝ × ℝ => F (boxPoint q.1 q.2))
      (Icc tl tr ×ˢ Icc sb st) :=
    hF.comp (by unfold boxPoint; fun_prop) (fun q hq => boxPoint_mem hq.1 hq.2)
  exact hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem rectangleIntegral_eq_closed_area (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st F =
      ∫ q in Icc tl tr ×ˢ Icc sb st, F (boxPoint q.1 q.2) := by
  rw [rectangleIntegral_swap ht hs hF]
  simp_rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le hs,
    ← integral_Icc_eq_integral_Ioc]
  have hi : IntegrableOn (fun q : ℝ × ℝ => F (boxPoint q.1 q.2))
      (Icc tl tr ×ˢ Icc sb st) (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod] using coordinateRectangle_closed_area_integrable hF
  simpa only [← Measure.volume_eq_prod] using
    (setIntegral_prod (fun q : ℝ × ℝ => F (boxPoint q.1 q.2)) hi).symm

variable {U : Set Coord} {K G1 B C u f : Coord → ℝ}
  {l0 l1 r1 r0 a0 a1 b c c1 MK g0 M : ℝ}

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Metric Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem continuous_intervalIntegral_of_joint
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    {a b : ℝ} (hab : a ≤ b) {f : X → ℝ → ℝ}
    (hf : Continuous (fun p : X × Icc a b => f p.1 p.2)) :
    Continuous (fun x => ∫ u in a..b, f x u) := by
  let g : X → ℝ → ℝ := fun x u => f x (projIcc a b hab u)
  have hg : Continuous (uncurry g) :=
    hf.comp (continuous_fst.prodMk ((continuous_projIcc (h := hab)).comp continuous_snd))
  have hc : Continuous (fun x => ∫ u in Icc a b, g x u) :=
    continuous_parametric_integral_of_continuous hg isCompact_Icc
  apply hc.congr
  intro x
  calc
    (∫ u in Icc a b, g x u) = ∫ u in a..b, g x u := by
      rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
    _ = ∫ u in a..b, f x u := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc a b := by simpa only [uIcc_of_le hab] using hu
      simp only [g, projIcc_of_mem hab hu']

abbrev CapInterval := Icc (-2 : ℝ) 2
abbrev VerticalInterval := Icc (-3 : ℝ) 3

theorem verticalAverageDerivative_continuous {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) :
    Continuous (fun p : CapInterval × (VerticalInterval × VerticalInterval) =>
      verticalAverageDerivative q p.1 p.2.1 p.2.2) := by
  apply continuous_intervalIntegral_of_joint (show (0 : ℝ) ≤ 1 by norm_num)
  have hmap : Continuous
      (fun p : (CapInterval × (VerticalInterval × VerticalInterval)) × Icc (0 : ℝ) 1 =>
        coordinatePoint p.1.1 ((p.1.2.1 : ℝ) + p.2 * ((p.1.2.2 : ℝ) - p.1.2.1))) := by
    unfold coordinatePoint
    fun_prop
  exact (partial_contDiffOn hq hU 1).continuousOn.comp_continuous hmap
    (fun p => hSU (verticalSegment_mem_modelSquare p.1.1.2 p.1.2.1.2 p.1.2.2.2 p.2.2))

def flowAverageCoefficient (q : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (s0 s1 t : ℝ) : ℝ :=
  verticalAverageDerivative q t (Y s0 t) (Y s1 t)

theorem flowAverageCoefficient_continuous {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {Y : ℝ → ℝ → ℝ}
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3) :
    Continuous (fun p : CapInterval × (CapInterval × CapInterval) =>
      flowAverageCoefficient q Y p.1 p.2.1 p.2.2) := by
  have hy0 : Continuous (fun p : CapInterval × (CapInterval × CapInterval) =>
      Y p.1 p.2.2) :=
    hY.comp_continuous
      (f := fun p : CapInterval × (CapInterval × CapInterval) => ((p.1 : ℝ), (p.2.2 : ℝ)))
      (by fun_prop) (fun p => ⟨p.1.2, p.2.2.2⟩)
  have hy1 : Continuous (fun p : CapInterval × (CapInterval × CapInterval) =>
      Y p.2.1 p.2.2) :=
    hY.comp_continuous
      (f := fun p : CapInterval × (CapInterval × CapInterval) => ((p.2.1 : ℝ), (p.2.2 : ℝ)))
      (by fun_prop) (fun p => ⟨p.2.1.2, p.2.2.2⟩)
  have hmap : Continuous
      (fun p : CapInterval × (CapInterval × CapInterval) =>
        (p.2.2, ((⟨Y p.1 p.2.2, hrange _ p.1.2 _ p.2.2.2⟩,
          ⟨Y p.2.1 p.2.2, hrange _ p.2.1.2 _ p.2.2.2⟩) :
          VerticalInterval × VerticalInterval))) :=
    (continuous_snd.snd).prodMk
      ((hy0.subtype_mk _).prodMk (hy1.subtype_mk _))
  exact (verticalAverageDerivative_continuous hq hU hSU).comp hmap

theorem flowAverageIntegral_continuous {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {Y : ℝ → ℝ → ℝ}
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3) {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) :
    Continuous (fun p : CapInterval × CapInterval =>
      ∫ u in 0..t, flowAverageCoefficient q Y p.1 p.2 u) := by
  have hcoeff := flowAverageCoefficient_continuous hq hU hSU hY hrange
  have haux (a b : ℝ) (hab : a ≤ b) (ha : -2 ≤ a) (hb : b ≤ 2) :
      Continuous (fun p : CapInterval × CapInterval =>
        ∫ u in a..b, flowAverageCoefficient q Y p.1 p.2 u) := by
    apply continuous_intervalIntegral_of_joint hab
    have hmap : Continuous
        (fun p : (CapInterval × CapInterval) × Icc a b =>
          (p.1.1, (p.1.2, (⟨p.2, ⟨ha.trans p.2.2.1, p.2.2.2.trans hb⟩⟩ : CapInterval)))) := by
      fun_prop
    exact hcoeff.comp hmap
  by_cases ht0 : 0 ≤ t
  · exact haux 0 t ht0 (by norm_num) ht.2
  · have hc := (haux t 0 (le_of_not_ge ht0) ht.1 (by norm_num)).neg
    apply hc.congr
    intro p
    exact (intervalIntegral.integral_symm _ _).symm

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Metric Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem hasDerivAt_of_exact_secant {f g : ℝ → ℝ} {s : ℝ}
    (hg : ContinuousAt g s)
    (he : ∀ᶠ u in 𝓝 s, f u - f s = (u - s) * g u) :
    HasDerivAt f (g s) s := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hslope : slope f s =ᶠ[𝓝[≠] s] g := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hne
    have hne' : u ≠ s := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
    rw [slope_def_field, hu]
    exact mul_div_cancel_left₀ (g u) (sub_ne_zero.mpr hne')
  exact (hg.mono_left nhdsWithin_le_nhds).congr' hslope.symm

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem flow_difference_formula
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {s0 s1 t : ℝ} (hs0 : s0 ∈ Icc (-2 : ℝ) 2) (hs1 : s1 ∈ Icc (-2 : ℝ) 2)
    (ht : t ∈ Ioo (-2 : ℝ) 2) :
    Y s1 t - Y s0 t = (s1 - s0) *
      Real.exp (-(∫ u in 0..t, flowAverageCoefficient q Y s0 s1 u)) := by
  have hcoeff := flowAverageCoefficient_continuous hq hU hSU hY hrange
  have ha : ContinuousOn (flowAverageCoefficient q Y s0 s1) (Icc (-2 : ℝ) 2) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hcoeff.comp
      ((continuous_const (y := (⟨s0, hs0⟩ : CapInterval))).prodMk
        ((continuous_const (y := (⟨s1, hs1⟩ : CapInterval))).prodMk continuous_id))
  have hz (u : ℝ) (hu : u ∈ Ioo (-2 : ℝ) 2) :
      HasDerivAt (fun v => Y s1 v - Y s0 v)
        (-flowAverageCoefficient q Y s0 s1 u * (Y s1 u - Y s0 u)) u := by
    exact (flow_difference_hasDerivWithinAt hq hU hSU ⟨hu.1.le, hu.2.le⟩
      (hrange s0 hs0 u ⟨hu.1.le, hu.2.le⟩) (hrange s1 hs1 u ⟨hu.1.le, hu.2.le⟩)
      (hode s0 hs0 u ⟨hu.1.le, hu.2.le⟩) (hode s1 hs1 u ⟨hu.1.le, hu.2.le⟩)).hasDerivAt
        (Icc_mem_nhds hu.1 hu.2)
  have he := scalar_linear_evolution_formula (show (0 : ℝ) < 2 by norm_num)
    (ha.mono Ioo_subset_Icc_self) hz ht
  simpa only [hstart s0 hs0, hstart s1 hs1] using he

theorem cap_flow_hasDerivAt_initial
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => Y u t)
      (Real.exp (-(∫ r in 0..t, coordPartial 1 q (coordinatePoint r (Y s r))))) s := by
  let G (u : ℝ) := Real.exp (-(∫ r in 0..t, flowAverageCoefficient q Y s u r))
  have hG : ContinuousOn G (Icc (-2 : ℝ) 2) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (((flowAverageIntegral_continuous hq hU hSU hY hrange
      ⟨ht.1.le, ht.2.le⟩).comp
        ((continuous_const (y := (⟨s, ⟨hs.1.le, hs.2.le⟩⟩ : CapInterval))).prodMk continuous_id)).neg).rexp
  have he : ∀ᶠ u in 𝓝 s, Y u t - Y s t = (u - s) * G u := by
    filter_upwards [Icc_mem_nhds hs.1 hs.2] with u hu
    exact flow_difference_formula hq hU hSU hY hrange hstart hode ⟨hs.1.le, hs.2.le⟩ hu ht
  have hd := hasDerivAt_of_exact_secant (hG.continuousAt (Icc_mem_nhds hs.1 hs.2)) he
  have hdiag : G s = Real.exp (-(∫ r in 0..t,
      coordPartial 1 q (coordinatePoint r (Y s r)))) := by
    simp only [G, flowAverageCoefficient, verticalAverageDerivative_diagonal]
  rw [hdiag] at hd
  exact hd

theorem cap_flow_initial_deriv_pos
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    0 < deriv (fun u => Y u t) s := by
  rw [(cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hs ht).deriv]
  exact Real.exp_pos _

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def flowCoordinateMap (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Coord :=
  coordinatePoint p.1 (Y p.2 p.1)

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem cap_flow_joint_contDiffOn
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) := by
  let D := pairRectangle 2 (-2) 2
  let F (p : ℝ × ℝ) := Y p.2 p.1
  let B (p : ℝ × ℝ) := coordPartial 1 q (flowCoordinateMap Y p)
  have hmem : MapsTo (flowCoordinateMap Y) D U := by
    intro p hp
    exact hSU (coordinatePoint_mem_modelSquare
      ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
      (hrange p.2 ⟨hp.2.1.le, hp.2.2.le⟩ p.1 ⟨hp.1.1.le, hp.1.2.le⟩))
  have hdx (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun x => F (x, p.2)) (-q (flowCoordinateMap Y p)) p.1 := by
    exact (hode p.2 ⟨hp.2.1.le, hp.2.2.le⟩ p.1 ⟨hp.1.1.le, hp.1.2.le⟩).hasDerivAt
      (Icc_mem_nhds hp.1.1 hp.1.2)
  have hdy (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun y => F (p.1, y)) (Real.exp (-pairPrimitive B p)) p.2 := by
    exact cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hp.2 hp.1
  have hnat : ∀ n : ℕ, ContDiffOn ℝ n F D := by
    intro n
    induction n with
    | zero =>
        have hc : ContinuousOn F D := hY.comp continuous_swap.continuousOn
          (fun p hp => ⟨⟨hp.2.1.le, hp.2.2.le⟩, ⟨hp.1.1.le, hp.1.2.le⟩⟩)
        simpa only [Nat.cast_zero, contDiffOn_zero] using hc
    | succ n hn =>
        have horder : (n : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
        have hmap : ContDiffOn ℝ n (flowCoordinateMap Y) D := by
          exact (contDiffOn_fst.smul contDiffOn_const).add (hn.smul contDiffOn_const)
        have hfx : ContDiffOn ℝ n (fun p => -q (flowCoordinateMap Y p)) D :=
          ((hq.of_le horder).comp hmap hmem).neg
        have hB : ContDiffOn ℝ n B D :=
          ((partial_contDiffOn hq hU 1).of_le horder).comp hmap hmem
        have hfy : ContDiffOn ℝ n (fun p => Real.exp (-pairPrimitive B p)) D :=
          ((pairPrimitive_contDiffOn_nat n hB).neg).exp
        exact contDiffOn_succ_of_continuous_partials (pairRectangle_isOpen 2 (-2) 2) n
          hfx hfy hdx hdy
  exact contDiffOn_infty.mpr hnat

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

theorem capChartDomain_isOpen : IsOpen capChartDomain := coordinateRectangle_isOpen _ _ _

theorem capChart_zero (Y : ℝ → ℝ → ℝ) (p : Coord) : capChart Y p 0 = p 0 := by
  simp [capChart, coordinatePoint]

theorem capChart_one (Y : ℝ → ℝ → ℝ) (p : Coord) : capChart Y p 1 = capFlowHeight Y p := by
  simp [capChart, coordinatePoint]

variable {Y : ℝ → ℝ → ℝ}

theorem capFlowHeight_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)) :
    ContDiffOn ℝ ∞ (capFlowHeight Y) capChartDomain := by
  exact hY.comp ((contDiffOn_apply ℝ ℝ 0 _).prodMk (contDiffOn_apply ℝ ℝ 1 _))
    (fun p hp => hp)

theorem capChart_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)) :
    ContDiffOn ℝ ∞ (capChart Y) capChartDomain := by
  exact ((contDiffOn_apply ℝ ℝ 0 _).smul contDiffOn_const).add
    ((capFlowHeight_contDiffOn hY).smul contDiffOn_const)

theorem boxPoint_coord_eta (p : Coord) : boxPoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> simp [boxPoint]

theorem capFlowHeight_hasDerivAt_time {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) :
    HasDerivAt (Y (p 1)) (coordPartial 0 (capFlowHeight Y) p) (p 0) := by
  have hd : DifferentiableAt ℝ (capFlowHeight Y) p :=
    ((capFlowHeight_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hd' : DifferentiableAt ℝ (capFlowHeight Y) (boxPoint (p 0) (p 1)) := by
    simpa only [boxPoint_coord_eta] using hd
  have hline := hd'.hasFDerivAt.comp_hasDerivAt (p 0) (boxPoint_hasDerivAt_t (p 0) (p 1))
  change HasDerivAt (fun t => capFlowHeight Y (boxPoint t (p 1)))
    (coordPartial 0 (capFlowHeight Y) (boxPoint (p 0) (p 1))) (p 0) at hline
  have hfun : (fun t => capFlowHeight Y (boxPoint t (p 1))) = Y (p 1) := by
    funext t
    simp [capFlowHeight, boxPoint]
  rw [hfun, boxPoint_coord_eta] at hline
  exact hline

theorem capFlowHeight_hasDerivAt_initial {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) :
    HasDerivAt (fun s => Y s (p 0)) (coordPartial 1 (capFlowHeight Y) p) (p 1) := by
  have hd : DifferentiableAt ℝ (capFlowHeight Y) p :=
    ((capFlowHeight_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hd' : DifferentiableAt ℝ (capFlowHeight Y) (boxPoint (p 0) (p 1)) := by
    simpa only [boxPoint_coord_eta] using hd
  have hline := hd'.hasFDerivAt.comp_hasDerivAt (p 1) (boxPoint_hasDerivAt_s (p 0) (p 1))
  change HasDerivAt (fun s => capFlowHeight Y (boxPoint (p 0) s))
    (coordPartial 1 (capFlowHeight Y) (boxPoint (p 0) (p 1))) (p 1) at hline
  have hfun : (fun s => capFlowHeight Y (boxPoint (p 0) s)) = (fun s => Y s (p 0)) := by
    funext s
    simp [capFlowHeight, boxPoint]
  rw [hfun, boxPoint_coord_eta] at hline
  exact hline

variable {q : Coord → ℝ}

theorem capFlowHeight_partial_time {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hp : p ∈ capChartDomain) :
    coordPartial 0 (capFlowHeight Y) p = -q (capChart Y p) := by
  have ht : p 0 ∈ Ioo (-2 : ℝ) 2 := hp.1
  have hs : p 1 ∈ Ioo (-2 : ℝ) 2 := hp.2
  have ho := (hode (p 1) ⟨hs.1.le, hs.2.le⟩ (p 0) ⟨ht.1.le, ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  exact (capFlowHeight_hasDerivAt_time hY hp).unique ho

theorem capFlowHeight_partial_initial_pos {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) : 0 < coordPartial 1 (capFlowHeight Y) p := by
  rw [← (capFlowHeight_hasDerivAt_initial hY hp).deriv]
  exact hvar (p 1) hp.2 (p 0) hp.1

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.ODE

theorem exists_open_hessianQuotient_domain
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hSU : modelSquare ⊆ U)
    (hyy : ∀ p ∈ modelSquare, covHessian g z p 1 1 ≠ 0) :
    ∃ V : Set Coord, IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      (∀ p ∈ V, covHessian g z p 1 1 ≠ 0) ∧
      ContDiffOn ℝ ∞ (hessianQuotient g z) V := by
  let V := U ∩ (fun p => covHessian g z p 1 1) ⁻¹' ({0} : Set ℝ)ᶜ
  have hV : IsOpen V :=
    (covHessian_contDiffOn hg hU hz 1 1).continuousOn.isOpen_inter_preimage
      hU isClosed_singleton.isOpen_compl
  have hVU : V ⊆ U := fun _ hp => hp.1
  have hSV : modelSquare ⊆ V := fun p hp => ⟨hSU hp, hyy p hp⟩
  have hnonzero : ∀ p ∈ V, covHessian g z p 1 1 ≠ 0 := fun _ hp => hp.2
  have hgv : SmoothPositiveOn g V :=
    ⟨fun i j => (hg.1 i j).mono hVU, fun p hp => hg.2 p (hVU hp)⟩
  exact ⟨V, hV, hSV, hVU, hnonzero,
    hessianQuotient_contDiffOn hgv hV (hz.mono hVU) hnonzero⟩

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem flow_initial_integral_bound
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    {M : ℝ} (hM : 0 ≤ M) (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    {s t : ℝ} (hs : s ∈ Icc (-2 : ℝ) 2) (ht : t ∈ Icc (-2 : ℝ) 2) :
    IntervalIntegrable (fun r => coordPartial 1 q (coordinatePoint r (Y s r))) volume 0 t ∧
      |∫ r in 0..t, coordPartial 1 q (coordinatePoint r (Y s r))| ≤ 2 * M := by
  have hmem (u : ℝ) (hu : u ∈ Icc (-2 : ℝ) 2) :
      coordinatePoint u (Y s u) ∈ modelSquare :=
    coordinatePoint_mem_modelSquare ⟨by linarith [hu.1], by linarith [hu.2]⟩ (hrange s hs u hu)
  have hy : ContinuousOn (Y s) (Icc (-2 : ℝ) 2) :=
    hY.comp (f := fun u : ℝ => (s, u)) (by fun_prop) (fun u hu => ⟨hs, hu⟩)
  have hmap : ContinuousOn (fun u => coordinatePoint u (Y s u)) (Icc (-2 : ℝ) 2) :=
    (continuousOn_id.smul continuousOn_const).add (hy.smul continuousOn_const)
  have hc : ContinuousOn (fun u => coordPartial 1 q (coordinatePoint u (Y s u)))
      (Icc (-2 : ℝ) 2) :=
    (partial_contDiffOn hq hU 1).continuousOn.comp hmap (fun u hu => hSU (hmem u hu))
  have hseg : uIcc (0 : ℝ) t ⊆ Icc (-2 : ℝ) 2 :=
    uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ ht
  refine ⟨(hc.mono hseg).intervalIntegrable, ?_⟩
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := M)
    (f := fun u => coordPartial 1 q (coordinatePoint u (Y s u)))
    (fun u hu => by
      rw [Real.norm_eq_abs]
      exact hMq _ (hmem u (hseg (uIoc_subset_uIcc hu))))
  have ht2 : |t| ≤ 2 := abs_le.mpr ht
  calc
    _ ≤ M * |t| := by simpa only [Real.norm_eq_abs, sub_zero] using hh
    _ ≤ M * 2 := mul_le_mul_of_nonneg_left ht2 hM
    _ = 2 * M := mul_comm _ _

theorem cap_flow_initial_deriv_bounds
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {M : ℝ} (hM : 0 ≤ M) (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    Real.exp (-2 * M) ≤ deriv (fun u => Y u t) s ∧
      deriv (fun u => Y u t) s ≤ Real.exp (2 * M) := by
  have hI := (flow_initial_integral_bound hq hU hSU hY hrange hM hMq
    ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩).2
  rw [(cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hs ht).deriv]
  constructor
  · apply Real.exp_monotone
    linarith [(abs_le.mp hI).2]
  · apply Real.exp_monotone
    linarith [(abs_le.mp hI).1]

def triangularFlow (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1, Y p.2 p.1)

theorem cap_flow_strictMonoOn_initial
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    StrictMonoOn (fun s => Y s t) (Ioo (-2 : ℝ) 2) := by
  have hc : ContinuousOn (fun s => Y s t) (Ioo (-2 : ℝ) 2) :=
    HasDerivAt.continuousOn
      (fun s hs => cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hs ht)
  apply strictMonoOn_of_deriv_pos (convex_Ioo (-2 : ℝ) 2) hc
  intro s hs
  apply cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode _ ht
  simpa only [interior_Ioo] using hs

theorem triangularFlow_injOn
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) :
    InjOn (triangularFlow Y) (pairRectangle 2 (-2) 2) := by
  intro p hp z hz he
  have ht : p.1 = z.1 := by
    simpa only [triangularFlow] using congrArg (fun v : ℝ × ℝ => v.1) he
  have hy : Y p.2 p.1 = Y z.2 z.1 := by
    simpa only [triangularFlow] using congrArg (fun v : ℝ × ℝ => v.2) he
  rw [ht] at hy
  exact Prod.ext ht
    ((cap_flow_strictMonoOn_initial hq hU hSU hY hrange hstart hode hz.1).injOn hp.2 hz.2 hy)

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def driftOperator (q a B C0 u : Coord → ℝ) (p : Coord) : ℝ :=
  coordinateDrift q (coordinateDrift q u) p + a p * coordPartial 1 (coordPartial 1 u) p +
    B p * coordinateDrift q u p + C0 p * coordPartial 1 u p

variable {Y : ℝ → ℝ → ℝ} {u q : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem capChart_partial
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (i : Fin 2) :
    coordPartial i (capChart Y) p =
      (if i = 0 then Pi.single 0 (1 : ℝ) else 0) +
        coordPartial i (capFlowHeight Y) p • Pi.single 1 (1 : ℝ) := by
  have hheight : DifferentiableAt ℝ (capFlowHeight Y) p :=
    ((capFlowHeight_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hd : HasFDerivAt (fun z : Coord => z 0 • (Pi.single 0 (1 : ℝ) : Coord) +
      capFlowHeight Y z • (Pi.single 1 (1 : ℝ) : Coord))
      ((ContinuousLinearMap.proj 0).smulRight (Pi.single 0 (1 : ℝ) : Coord) +
        (fderiv ℝ (capFlowHeight Y) p).smulRight (Pi.single 1 (1 : ℝ) : Coord)) p :=
    ((hasFDerivAt_apply (𝕜 := ℝ) 0 p).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add
      (hheight.hasFDerivAt.smul_const (Pi.single 1 (1 : ℝ) : Coord))
  change fderiv ℝ (fun z : Coord => z 0 • (Pi.single 0 (1 : ℝ) : Coord) +
    capFlowHeight Y z • (Pi.single 1 (1 : ℝ) : Coord)) p (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;> simp [coordPartial]

theorem capPullback_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hu : ContDiffOn ℝ ∞ u U) (hmap : MapsTo (capChart Y) capChartDomain U) :
    ContDiffOn ℝ ∞ (capPullback Y u) capChartDomain :=
  hu.comp (capChart_contDiffOn hY) hmap

theorem capPullback_partial
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (hu : DifferentiableAt ℝ u (capChart Y p)) (i : Fin 2) :
    coordPartial i (capPullback Y u) p =
      (if i = 0 then coordPartial 0 u (capChart Y p) else 0) +
        coordPartial 1 u (capChart Y p) * coordPartial i (capFlowHeight Y) p := by
  have hchart : DifferentiableAt ℝ (capChart Y) p :=
    ((capChart_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  change fderiv ℝ (u ∘ capChart Y) p (Pi.single i 1) = _
  rw [fderiv_comp p hu hchart, ContinuousLinearMap.comp_apply]
  change fderiv ℝ u (capChart Y p) (coordPartial i (capChart Y) p) = _
  rw [capChart_partial hY hp i]
  fin_cases i <;> simp [coordPartial, smul_eq_mul] <;> ring

theorem capPullback_partial_initial
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (hu : DifferentiableAt ℝ u (capChart Y p)) :
    coordPartial 1 (capPullback Y u) p =
      capPullback Y (coordPartial 1 u) p * coordPartial 1 (capFlowHeight Y) p := by
  simpa only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, zero_add, capPullback] using
    capPullback_partial hY hp hu 1

theorem capPullback_partial_time
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hp : p ∈ capChartDomain) (hu : DifferentiableAt ℝ u (capChart Y p)) :
    coordPartial 0 (capPullback Y u) p = coordinateDrift q u (capChart Y p) := by
  rw [capPullback_partial hY hp hu 0, capFlowHeight_partial_time hY hode hp]
  simp only [↓reduceIte, coordinateDrift]
  ring

theorem capPullback_original_y
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) (hu : DifferentiableAt ℝ u (capChart Y p)) :
    capPullback Y (coordPartial 1 u) p = capChartRho Y p * coordPartial 1 (capPullback Y u) p := by
  rw [capPullback_partial_initial hY hp hu, capChartRho]
  field_simp [(capFlowHeight_partial_initial_pos hY hvar hp).ne']

theorem capPullback_second_initial_forward
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    coordPartial 1 (coordPartial 1 (capPullback Y u)) p =
      capPullback Y (coordPartial 1 (coordPartial 1 u)) p *
          (coordPartial 1 (capFlowHeight Y) p) ^ 2 +
        capPullback Y (coordPartial 1 u) p * coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p := by
  have huy := partial_contDiffOn hu hU 1
  have hPuy := capPullback_contDiffOn hY huy hmap
  have hYs := partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1
  have he : coordPartial 1 (capPullback Y u) =ᶠ[𝓝 p]
      (fun z => capPullback Y (coordPartial 1 u) z * coordPartial 1 (capFlowHeight Y) z) := by
    filter_upwards [capChartDomain_isOpen.mem_nhds hp] with z hz
    exact capPullback_partial_initial hY hz
      ((hu.contDiffAt (hU.mem_nhds (hmap hz))).differentiableAt (by simp))
  have hd := congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single 1 (1 : ℝ))) he.fderiv_eq
  change coordPartial 1 (coordPartial 1 (capPullback Y u)) p =
    coordPartial 1 (fun z => capPullback Y (coordPartial 1 u) z * coordPartial 1 (capFlowHeight Y) z) p at hd
  rw [hd, HessianCalculus.coordPartial_mul_at
    ((hPuy.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp))
    ((hYs.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)) 1,
    capPullback_partial_initial hY hp
      ((huy.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp))]
  ring

theorem capPullback_original_yy
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    capPullback Y (coordPartial 1 (coordPartial 1 u)) p =
      (capChartRho Y p) ^ 2 * coordPartial 1 (coordPartial 1 (capPullback Y u)) p +
        capChartSigma Y p * coordPartial 1 (capPullback Y u) p := by
  rw [capPullback_second_initial_forward hY hu hU hmap hp,
    capPullback_partial_initial hY hp
      ((hu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp))]
  unfold capChartRho capChartSigma
  field_simp [(capFlowHeight_partial_initial_pos hY hvar hp).ne']
  ring

theorem coordinateDrift_contDiffOn (hq : ContDiffOn ℝ ∞ q U)
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (coordinateDrift q u) U :=
  (partial_contDiffOn hu hU 0).sub (hq.mul (partial_contDiffOn hu hU 1))

theorem capPullback_drift_twice
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hq : ContDiffOn ℝ ∞ q U) (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    capPullback Y (coordinateDrift q (coordinateDrift q u)) p =
      coordPartial 0 (coordPartial 0 (capPullback Y u)) p := by
  have hDu := coordinateDrift_contDiffOn hq hu hU
  have he : coordPartial 0 (capPullback Y u) =ᶠ[𝓝 p] capPullback Y (coordinateDrift q u) := by
    filter_upwards [capChartDomain_isOpen.mem_nhds hp] with z hz
    exact capPullback_partial_time hY hode hz
      ((hu.contDiffAt (hU.mem_nhds (hmap hz))).differentiableAt (by simp))
  have hd := congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single 0 (1 : ℝ))) he.fderiv_eq
  change coordPartial 0 (coordPartial 0 (capPullback Y u)) p =
    coordPartial 0 (capPullback Y (coordinateDrift q u)) p at hd
  rw [hd, capPullback_partial_time hY hode hp
    ((hDu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp))]
  rfl

theorem cap_driftOperator_transport (a B C0 : Coord → ℝ)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hq : ContDiffOn ℝ ∞ q U) (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    capPullback Y (driftOperator q a B C0 u) p =
      multiplierOperator (capTransportA Y a) (capPullback Y B)
        (capTransportC Y a C0) (capPullback Y u) p := by
  have hud := ((hu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp))
  change capPullback Y (coordinateDrift q (coordinateDrift q u)) p +
    a (capChart Y p) * capPullback Y (coordPartial 1 (coordPartial 1 u)) p +
    B (capChart Y p) * coordinateDrift q u (capChart Y p) +
    C0 (capChart Y p) * capPullback Y (coordPartial 1 u) p = _
  rw [capPullback_drift_twice hY hode hq hu hU hmap hp,
    capPullback_original_yy hY hvar hu hU hmap hp,
    ← capPullback_partial_time hY hode hp hud,
    capPullback_original_y hY hvar hp hud]
  unfold multiplierOperator capTransportA capTransportC capPullback
  ring

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.ODE

theorem modelSquare_closure_interior : closure (interior modelSquare) = modelSquare := by
  unfold modelSquare
  rw [← Set.pi_univ_Icc, interior_pi_set (Set.finite_univ : (Set.univ : Set (Fin 2)).Finite)]
  simp only [interior_Icc, closure_pi_set,
    closure_Ioo (by norm_num : (-3 : ℝ) ≠ 3), Set.pi_univ_Icc]

theorem CoordinateBound.restrict_domain {f : Coord → ℝ} {S T : Set Coord} {n : ℕ} {M : ℝ}
    (hf : CoordinateBound f S n M) (hTS : T ⊆ S) : CoordinateBound f T n M :=
  fun ds hds p hp => hf ds hds p (hTS hp)

theorem CoordinateBound.of_modelSquare_interior {f : Coord → ℝ} {U : Set Coord} {n : ℕ} {M : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hB : CoordinateBound f (interior modelSquare) n M) : CoordinateBound f modelSquare n M := by
  intro ds hds p hp
  have hcont : ContinuousOn (fun x => |iteratedCoordPartial ds f x|) modelSquare :=
    ((LowQuotient.iterated_contDiffOn hf hU ds).continuousOn.mono hSU).abs
  have hcl : p ∈ closure (interior modelSquare) := by rw [modelSquare_closure_interior]; exact hp
  apply le_on_closure (fun x hx => hB ds hds x hx) _ continuousOn_const hcl
  rw [modelSquare_closure_interior]
  exact hcont

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}

theorem exists_open_quotient_domain_with_closed_low_bounds
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) :
    ∃ V : Set Coord, IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      (∀ p ∈ V, covHessian g z p 1 1 ≠ 0) ∧
      ContDiffOn ℝ ∞ (hessianQuotient g z) V ∧
      CoordinateBound (hessianQuotient g z) modelSquare 3
        (LowQuotient.boundThroughThree (hessianJetBound G Z d) c) := by
  obtain ⟨V, hV, hSV, hVU, hVne, hqV⟩ := exists_open_hessianQuotient_domain hg hU hz hSU
    (LowQuotient.denominator_ne_zero hc hyy)
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun a b => (hg.1 a b).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  have hBI := (hessianQuotient_bound_from_metric_height_jets hgI isOpen_interior (hz.mono hIU)
    hG hZ hd hc (fun a b => (hgB a b).restrict_domain interior_subset)
    (hzB.restrict_domain interior_subset) (fun p hp => hdet p (interior_subset hp))
    (fun p hp => hyy p (interior_subset hp))).2
  exact ⟨V, hV, hSV, hVU, hVne, hqV,
    CoordinateBound.of_modelSquare_interior hqV hV hSV hBI⟩

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def triangularLinearEquiv (a b : ℝ) (hb : b ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun v := (v.1, a * v.1 + b * v.2)
  invFun w := (w.1, (w.2 - a * w.1) / b)
  left_inv v := by
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [hb]
      ring
  right_inv w := by
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [hb]
      ring
  map_add' v w := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add]
    ring
  map_smul' c v := by
    apply Prod.ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem triangularFlow_hasFDerivAt_equiv
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {p : ℝ × ℝ} (hp : p ∈ pairRectangle 2 (-2) 2) :
    ∃ A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), HasFDerivAt (triangularFlow Y) (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
  let F (v : ℝ × ℝ) := Y v.2 v.1
  let a := -q (coordinatePoint p.1 (Y p.2 p.1))
  let b := Real.exp (-(∫ r in 0..p.1, coordPartial 1 q (coordinatePoint r (Y p.2 r))))
  have hF : ContDiffOn ℝ ∞ F (pairRectangle 2 (-2) 2) :=
    cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hd := ((hF.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt
  have hdx : HasDerivAt (fun t => F (t, p.2)) a p.1 :=
    (hode p.2 ⟨hp.2.1.le, hp.2.2.le⟩ p.1 ⟨hp.1.1.le, hp.1.2.le⟩).hasDerivAt
      (Icc_mem_nhds hp.1.1 hp.1.2)
  have hdy : HasDerivAt (fun s => F (p.1, s)) b p.2 :=
    cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hp.2 hp.1
  have hdx' : HasDerivAt (fun t => F (t, p.2)) (fderiv ℝ F p (1, 0)) p.1 := by
    convert hd.comp_hasDerivAt p.1 ((hasDerivAt_id p.1).prodMk
      (hasDerivAt_const p.1 p.2)) using 1 <;> try with_reducible_and_instances rfl
    rfl
  have hdy' : HasDerivAt (fun s => F (p.1, s)) (fderiv ℝ F p (0, 1)) p.2 := by
    convert hd.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk
      (hasDerivAt_id p.2)) using 1 <;> try with_reducible_and_instances rfl
    rfl
  have hx : fderiv ℝ F p (1, 0) = a := hdx'.unique hdx
  have hy : fderiv ℝ F p (0, 1) = b := hdy'.unique hdy
  have hdeq : fderiv ℝ F p = jointDifferential a b := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = v.1 • ((1, 0) : ℝ × ℝ) + v.2 • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    calc
      fderiv ℝ F p v = v.1 * a + v.2 * b := by
        conv_lhs => rw [hv]
        simp only [map_add, map_smul, smul_eq_mul, hx, hy]
      _ = jointDifferential a b v := by simp [jointDifferential]
  have hFD : HasFDerivAt F (jointDifferential a b) p := hd.congr_fderiv hdeq
  have hb : b ≠ 0 := (Real.exp_pos _).ne'
  refine ⟨triangularLinearEquiv a b hb, ?_⟩
  have hTF := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk hFD
  convert hTF using 1 <;> first
    | rfl
    | (ext <;> simp [triangularLinearEquiv, jointDifferential])

theorem exists_triangularFlow_smooth_chart
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {p : ℝ × ℝ} (hp : p ∈ pairRectangle 2 (-2) 2) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      p ∈ e.source ∧ e.source ⊆ pairRectangle 2 (-2) 2 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let D := pairRectangle 2 (-2) 2
  have hD : IsOpen D := pairRectangle_isOpen 2 (-2) 2
  have hTF : ContDiffOn ℝ ∞ (triangularFlow Y) D :=
    contDiffOn_fst.prodMk (cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode)
  have hTFp := hTF.contDiffAt (hD.mem_nhds hp)
  obtain ⟨A, hA⟩ := triangularFlow_hasFDerivAt_equiv hq hU hSU hY hrange hstart hode hp
  let e0 := hTFp.toOpenPartialHomeomorph (triangularFlow Y) hA (by simp)
  let e := e0.restrOpen D hD
  have heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y := rfl
  have hsub : e.source ⊆ D := fun _ hx => hx.2
  refine ⟨e, ⟨hTFp.mem_toOpenPartialHomeomorph_source hA (by simp), hp⟩,
    hsub, heq, ?_, ?_⟩
  · rw [heq]
    exact hTF.mono hsub
  · intro y hy
    have hx : e.symm y ∈ D := hsub (e.map_target hy)
    obtain ⟨L, hL⟩ := triangularFlow_hasFDerivAt_equiv hq hU hSU hY hrange hstart hode hx
    have hLe : HasFDerivAt e (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (e.symm y) := by
      rw [heq]
      exact hL
    have hfe : ContDiffAt ℝ ∞ e (e.symm y) := by
      rw [heq]
      exact hTF.contDiffAt (hD.mem_nhds hx)
    exact (e.contDiffAt_symm hy hLe hfe).contDiffWithinAt

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

variable {g : MetricField} {z u : Coord → ℝ} {U : Set Coord} {p : Coord} {Y : ℝ → ℝ → ℝ}

theorem heightOriginalA_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (heightOriginalA g z) U :=
  (gaussianCurvature_contDiffOn hg hU).mul (darbouxG_contDiffOn hg hU hz hyy)

theorem height_coefficient_operator_transport
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-(hessianQuotient g z) (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hu : ContDiffOn ℝ ∞ u U)
    (hp : p ∈ capChartDomain) (ell : ℕ) :
    capPullback Y (driftOperator (hessianQuotient g z) (heightOriginalA g z)
      (heightOriginalB g z ell) (heightOriginalC0 g z ell) u) p =
      multiplierOperator (heightChartA g z Y) (heightChartB g z Y ell)
        (heightChartC g z Y ell) (capPullback Y u) p :=
  cap_driftOperator_transport _ _ _ hY hode hvar (hessianQuotient_contDiffOn hg hU hz hyy)
    hu hU hmap hp

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem exists_global_triangularFlow_chart
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      e.source = pairRectangle 2 (-2) 2 ∧
      e.target = triangularFlow Y '' pairRectangle 2 (-2) 2 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let D := pairRectangle 2 (-2) 2
  have hD : IsOpen D := pairRectangle_isOpen 2 (-2) 2
  have hTF : ContDiffOn ℝ ∞ (triangularFlow Y) D :=
    contDiffOn_fst.prodMk (cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode)
  have hinj : InjOn (triangularFlow Y) D := triangularFlow_injOn hq hU hSU hY hrange hstart hode
  have hlocal : IsLocalHomeomorphOn (triangularFlow Y) D := by
    intro x hx
    obtain ⟨e, he, hsub, heq, hf, hi⟩ :=
      exists_triangularFlow_smooth_chart hq hU hSU hY hrange hstart hode hx
    exact ⟨e, he, heq.symm⟩
  have hopen : IsOpenMap (D.domRestrict (triangularFlow Y)) := by
    apply IsOpenMap.of_nhds_le
    intro x
    have he : (𝓝 x).map (D.domRestrict (triangularFlow Y)) =
        𝓝 (triangularFlow Y x) := by
      change (𝓝 x).map ((triangularFlow Y) ∘ (Subtype.val : D → ℝ × ℝ)) = _
      rw [← Filter.map_map, hD.isOpenEmbedding_subtypeVal.map_nhds_eq,
        hlocal.map_nhds_eq x.2]
    exact he.ge
  let pe := hinj.toPartialEquiv (triangularFlow Y) D
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict pe hTF.continuousOn hopen hD
  have heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y := rfl
  have hsource : e.source = D := rfl
  refine ⟨e, hsource, rfl, heq, ?_, ?_⟩
  · rw [heq, hsource]
    exact hTF
  · intro y hy
    have hx : e.symm y ∈ D := by
      rw [← hsource]
      exact e.map_target hy
    obtain ⟨A, hA⟩ := triangularFlow_hasFDerivAt_equiv hq hU hSU hY hrange hstart hode hx
    have hAe : HasFDerivAt e (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (e.symm y) := by
      rw [heq]
      exact hA
    have hfe : ContDiffAt ℝ ∞ e (e.symm y) := by
      rw [heq]
      exact hTF.contDiffAt (hD.mem_nhds hx)
    exact (e.contDiffAt_symm hy hAe hfe).contDiffWithinAt

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem cap_trajectory_mem_ball_of_displacement {Y : ℝ → ℝ → ℝ}
    (hdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50)
    {s t : ℝ} (hs : s ∈ Ioo (-2:ℝ) 2) (ht : t ∈ Ioo (-2:ℝ) 2) :
    Y s t ∈ closedBall (0:ℝ) 3 := by
  have hp : coordinatePoint t s ∈ capChartDomain := by
    change coordinatePoint t s 0 ∈ Ioo (-2:ℝ) 2 ∧ coordinatePoint t s 1 ∈ Ioo (-2:ℝ) 2
    simpa [coordinatePoint] using (show t ∈ Ioo (-2:ℝ) 2 ∧ s ∈ Ioo (-2:ℝ) 2 from ⟨ht,hs⟩)
  have hd : |Y s t-s| ≤ (1:ℝ)/50 := by
    simpa [capFlowHeight,coordinatePoint] using hdisp (coordinatePoint t s) hp
  have hy : |Y s t| ≤ 3 := by
    have hh : |Y s t| ≤ |Y s t-s|+|s| := by
      simpa only [sub_add_cancel] using abs_add_le (Y s t-s) s
    have hs' : |s| < 2 := abs_lt.mpr hs
    linarith
  simpa only [mem_closedBall,Real.dist_eq,sub_zero] using hy

theorem capChart_eqOn_of_same_ode
    {q : Coord → ℝ} {U : Set Coord} {Y Z : ℝ → ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hYstart : ∀ s ∈ Icc (-2:ℝ) 2, Y s 0 = s)
    (hYode : ∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2:ℝ) 2) t)
    (hYdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50)
    (hZstart : ∀ s ∈ Icc (-2:ℝ) 2, Z s 0 = s)
    (hZode : ∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
      HasDerivWithinAt (Z s) (-q (coordinatePoint t (Z s t))) (Icc (-2:ℝ) 2) t)
    (hZdisp : ∀ p ∈ capChartDomain, |capFlowHeight Z p-p 1| ≤ (1:ℝ)/50) :
    EqOn (capChart Y) (capChart Z) capChartDomain := by
  obtain ⟨K,hK⟩ := exists_flowField_lipschitz hq hU hSU
  have hsame (s : ℝ) (hs : s ∈ Ioo (-2:ℝ) 2) : EqOn (Y s) (Z s) (Ioo (-2:ℝ) 2) := by
    have hs' : s ∈ Icc (-2:ℝ) 2 := ⟨hs.1.le,hs.2.le⟩
    apply ODE_solution_unique_of_mem_Ioo
      (v := flowField q) (s := fun _ => closedBall (0:ℝ) 3)
      (fun t ht => hK t ⟨ht.1.le,ht.2.le⟩) (t₀ := 0) (by norm_num)
    · intro t ht
      exact ⟨(hYode s hs' t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2),
        cap_trajectory_mem_ball_of_displacement hYdisp hs ht⟩
    · intro t ht
      exact ⟨(hZode s hs' t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2),
        cap_trajectory_mem_ball_of_displacement hZdisp hs ht⟩
    · rw [hYstart s hs',hZstart s hs']
  intro p hp
  unfold capChart capFlowHeight
  rw [hsame (p 1) hp.2 hp.1]

theorem capPullback_eventuallyEq_of_chart_eqOn {Y Z : ℝ → ℝ → ℝ}
    (heq : EqOn (capChart Y) (capChart Z) capChartDomain)
    (f : Coord → ℝ) {p : Coord} (hp : p ∈ capChartDomain) :
    capPullback Y f =ᶠ[𝓝 p] capPullback Z f := by
  filter_upwards [capChartDomain_isOpen.mem_nhds hp] with r hr
  exact congrArg f (heq hr)

theorem capPullback_square_rectangle_eq_of_chart_eqOn {Y Z : ℝ → ℝ → ℝ}
    (heq : EqOn (capChart Y) (capChart Z) capChartDomain)
    (f : Coord → ℝ) {tl tr sb st : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain) :
    rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) =
      rectangleIntegral tl tr sb st (fun p => (capPullback Z f p)^2) := by
  apply rectangleIntegral_congr ht hs
  intro p hp
  exact congrArg (fun x : Coord => (f x)^2) (heq (hbox hp))

theorem capPullback_gradient_rectangle_eq_of_chart_eqOn {Y Z : ℝ → ℝ → ℝ}
    (heq : EqOn (capChart Y) (capChart Z) capChartDomain)
    (f : Coord → ℝ) {tl tr sb st : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain) :
    rectangleIntegral tl tr sb st (fun p => (coordPartial 0 (capPullback Y f) p)^2+
        (coordPartial 1 (capPullback Y f) p)^2) =
      rectangleIntegral tl tr sb st (fun p => (coordPartial 0 (capPullback Z f) p)^2+
        (coordPartial 1 (capPullback Z f) p)^2) := by
  apply rectangleIntegral_congr ht hs
  intro p hp
  change (coordPartial 0 (capPullback Y f) p)^2 + (coordPartial 1 (capPullback Y f) p)^2 =
    (coordPartial 0 (capPullback Z f) p)^2 + (coordPartial 1 (capPullback Z f) p)^2
  rw [coordPartial_eq_of_eventuallyEq (capPullback_eventuallyEq_of_chart_eqOn heq f (hbox hp)) 0,
    coordPartial_eq_of_eventuallyEq (capPullback_eventuallyEq_of_chart_eqOn heq f (hbox hp)) 1]

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

theorem height_jetEnergy_first_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => coordPartial i (jetEnergy g p) (fun r => coordPartial r z p)) U := by
  have h0 := partial_contDiffOn hz hU 0
  have h1 := partial_contDiffOn hz hU 1
  fin_cases i
  · have hf : ContDiffOn ℝ ∞ (fun p => -2 * g p 1 1 * coordPartial 0 z p +
        (g p 0 1 + g p 1 0) * coordPartial 1 z p) U :=
      ((contDiffOn_const.mul (hg.1 1 1)).mul h0).add (((hg.1 0 1).add (hg.1 1 0)).mul h1)
    apply hf.congr
    intro p _
    simpa only [Fin.mk_zero, ↓reduceIte] using
      coordPartial_jetEnergy g p (fun r => coordPartial r z p) 0
  · have hf : ContDiffOn ℝ ∞ (fun p => (g p 0 1 + g p 1 0) * coordPartial 0 z p -
        2 * g p 0 0 * coordPartial 1 z p) U :=
      (((hg.1 0 1).add (hg.1 1 0)).mul h0).sub ((contDiffOn_const.mul (hg.1 0 0)).mul h1)
    apply hf.congr
    intro p _
    simpa only [Fin.mk_one, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] using
      coordPartial_jetEnergy g p (fun r => coordPartial r z p) 1

theorem height_christoffelAlongD_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => christoffelAlongD g p (hessianQuotient g z p) i) U := by
  have hq := hessianQuotient_contDiffOn hg hU hz hyy
  have hf : ContDiffOn ℝ ∞ (fun p => christoffel g i 0 0 p -
      2 * hessianQuotient g z p * christoffel g i 0 1 p +
      (hessianQuotient g z p)^2 * christoffel g i 1 1 p) U :=
    ((christoffel_contDiffOn hg hU i 0 0).sub
      ((contDiffOn_const.mul hq).mul (christoffel_contDiffOn hg hU i 0 1))).add
      ((hq.pow 2).mul (christoffel_contDiffOn hg hU i 1 1))
  exact hf.congr (fun p hp => christoffelAlongD_eq hg hU hp _ i)

theorem heightPFirst_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    ContDiffOn ℝ ∞ (heightPFirst g z i) U := by
  have hh := covHessian_contDiffOn hg hU hz 1 1
  have hf : ContDiffOn ℝ ∞ (fun p => christoffelAlongD g p (hessianQuotient g z p) i +
      gaussianCurvature g p *
        (coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) / covHessian g z p 1 1 +
          heightEnergy g z p * christoffel g i 1 1 p / (covHessian g z p 1 1)^2)) U :=
    (height_christoffelAlongD_contDiffOn hg hU hz hyy i).add
      ((gaussianCurvature_contDiffOn hg hU).mul
        (((height_jetEnergy_first_contDiffOn hg hU hz i).div hh hyy).add
          (((heightEnergy_contDiffOn hg hU hz).mul (christoffel_contDiffOn hg hU i 1 1)).div
            (hh.pow 2) (fun p hp => pow_ne_zero 2 (hyy p hp)))))
  exact hf.congr (fun p hp => heightPFirst_eq hg hU hp (hyy p hp) i)

end SmoothLocal.Geometry

namespace SmoothLocal.Flow
open SmoothLocal.Geometry

theorem heightOriginalB_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightOriginalB g z ell) U :=
  (heightPFirst_contDiffOn hg hU hz hyy 0).neg.sub
    (contDiffOn_const.mul (partial_contDiffOn (hessianQuotient_contDiffOn hg hU hz hyy) hU 1))

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem capChart_injOn_of_pairChart
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y) :
    InjOn (capChart Y) capChartDomain := by
  intro p hp r hr hsame
  have hp' : (p 0,p 1) ∈ e.source := by rw [hsource]; exact hp
  have hr' : (r 0,r 1) ∈ e.source := by rw [hsource]; exact hr
  have hpair : e (p 0,p 1) = e (r 0,r 1) := by
    rw [heq]
    apply Prod.ext
    · simpa only [triangularFlow,capChart_zero] using congrArg (fun q : Coord => q 0) hsame
    · simpa only [triangularFlow,capChart_one,capFlowHeight] using congrArg (fun q : Coord => q 1) hsame
  have hinj := e.injOn hp' hr' hpair
  ext i
  fin_cases i
  · exact congrArg Prod.fst hinj
  · exact congrArg Prod.snd hinj

theorem capChart_fderiv_matrix {Y : ℝ → ℝ → ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    {p : Coord} (hp : p ∈ capChartDomain) :
    LinearMap.toMatrix' (fderiv ℝ (capChart Y) p).toLinearMap =
      !![1,0; coordPartial 0 (capFlowHeight Y) p,coordPartial 1 (capFlowHeight Y) p] := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change coordPartial j (capChart Y) p i = _
  rw [capChart_partial hYs hp j]
  fin_cases i <;> fin_cases j <;> simp

theorem capChart_det_fderiv {Y : ℝ → ℝ → ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    {p : Coord} (hp : p ∈ capChartDomain) :
    (fderiv ℝ (capChart Y) p).det = coordPartial 1 (capFlowHeight Y) p := by
  rw [ContinuousLinearMap.det,←LinearMap.det_toMatrix',capChart_fderiv_matrix hYs hp]
  simp [Matrix.det_fin_two]

theorem capChart_abs_det_fderiv {Y : ℝ → ℝ → ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    {p : Coord} (hp : p ∈ capChartDomain) :
    |(fderiv ℝ (capChart Y) p).det| = coordPartial 1 (capFlowHeight Y) p := by
  rw [capChart_det_fderiv hYs hp,abs_of_pos (capFlowHeight_partial_initial_pos hYs hvar hp)]

theorem capChart_jacobian_bounds
    {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hM : 0 ≤ M) (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    {p : Coord} (hp : p ∈ capChartDomain) :
    Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
      coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M) := by
  have hYs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  rw [←(capFlowHeight_hasDerivAt_initial hYs hp).deriv]
  exact cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hp.2 hp.1

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem modelOpenSquare_isOpen : IsOpen modelOpenSquare := coordinateRectangle_isOpen _ _ _

theorem modelOpenSquare_subset : modelOpenSquare ⊆ modelSquare := by
  intro p hp
  constructor <;> intro i <;> fin_cases i
  · exact hp.1.1.le
  · exact hp.2.1.le
  · exact hp.1.2.le
  · exact hp.2.2.le

theorem capChart_mem_modelOpenSquare {Y : ℝ → ℝ → ℝ} {p : Coord}
    (hp : p ∈ capChartDomain) (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) :
    capChart Y p ∈ modelOpenSquare := by
  change (capChart Y p) 0 ∈ Ioo (-3 : ℝ) 3 ∧ (capChart Y p) 1 ∈ Ioo (-3 : ℝ) 3
  rw [capChart_zero, capChart_one]
  constructor
  · constructor <;> linarith [hp.1.1, hp.1.2]
  · constructor <;> linarith [hp.2.1, hp.2.2, (abs_le.mp hdisp).1, (abs_le.mp hdisp).2]

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Geometry.HessianCalculus

variable {q u a : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem coordinateDrift_twice_expanded
    (hq : ContDiffOn ℝ ∞ q U) (hu : ContDiffOn ℝ ∞ u U)
    (hU : IsOpen U) (hp : p ∈ U) :
    coordinateDrift q (coordinateDrift q u) p =
      coordPartial 0 (coordPartial 0 u) p -
        2 * q p * coordPartial 0 (coordPartial 1 u) p +
        (q p)^2 * coordPartial 1 (coordPartial 1 u) p -
        coordinateDrift q q p * coordPartial 1 u p := by
  have hqd : DifferentiableAt ℝ q p :=
    (hq.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hud (i : Fin 2) : DifferentiableAt ℝ (coordPartial i u) p :=
    ((partial_contDiffOn hu hU i).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hprod : DifferentiableAt ℝ (fun r => q r * coordPartial 1 u r) p := hqd.mul (hud 1)
  have hd (i : Fin 2) : coordPartial i (coordinateDrift q u) p =
      coordPartial i (coordPartial 0 u) p -
        (coordPartial i q p * coordPartial 1 u p + q p * coordPartial i (coordPartial 1 u) p) := by
    change coordPartial i (fun r => coordPartial 0 u r - q r * coordPartial 1 u r) p = _
    rw [coordPartial_sub_at (hud 0) hprod i, coordPartial_mul_at hqd (hud 1) i]
  change coordPartial 0 (coordinateDrift q u) p - q p * coordPartial 1 (coordinateDrift q u) p = _
  rw [hd 0, hd 1, coordPartial_comm hu hU hp 1 0]
  unfold coordinateDrift
  ring

theorem driftOperator_linearized_identity
    (hq : ContDiffOn ℝ ∞ q U) (hu : ContDiffOn ℝ ∞ u U)
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U) (hp : p ∈ U)
    (Px Py : Coord → ℝ) (ell : ℕ) :
    driftOperator q a
      (fun r => -Px r - 2 * (ell : ℝ) * coordPartial 1 q r)
      (fun r => coordinateDrift q q r - Px r * q r - Py r +
        (ell : ℝ) * coordPartial 1 a r) u p =
      coordPartial 0 (coordPartial 0 u) p -
        2 * q p * coordPartial 0 (coordPartial 1 u) p +
        ((q p)^2 + a p) * coordPartial 1 (coordPartial 1 u) p -
        Px p * coordPartial 0 u p - Py p * coordPartial 1 u p -
        (ell : ℝ) * (2 * coordPartial 1 q p * coordPartial 0 u p -
          coordPartial 1 (fun r => (q r)^2 + a r) p * coordPartial 1 u p) := by
  have hqd : DifferentiableAt ℝ q p :=
    (hq.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have had : DifferentiableAt ℝ a p :=
    (ha.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hqq : DifferentiableAt ℝ (fun r => q r * q r) p := hqd.mul hqd
  have htotal : coordPartial 1 (fun r => (q r)^2 + a r) p =
      2 * q p * coordPartial 1 q p + coordPartial 1 a p := by
    simp only [pow_two]
    rw [coordPartial_add_at hqq had 1, coordPartial_mul_at hqd hqd 1]
    ring
  unfold driftOperator
  rw [coordinateDrift_twice_expanded hq hu hU hp, htotal]
  unfold coordinateDrift
  ring

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem second_fderiv_comp_constant_direction
    {F : DarbouxState → ℝ} {J : Coord → DarbouxState} {p : Coord}
    (hF : ContDiffAt ℝ ∞ F (J p)) (hJ : DifferentiableAt ℝ J p) (v : DarbouxState) :
    iteratedFDeriv ℝ 2 F (J p) ![coordPartial 1 J p, v] =
      coordPartial 1 (fun r => fderiv ℝ F (J r) v) p := by
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) (J p) :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun r => fderiv ℝ F (J r)) p := hdF.comp p hJ
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold coordPartial
  have hcomp : fderiv ℝ (fun r => fderiv ℝ F (J r)) p =
      (fderiv ℝ (fderiv ℝ F) (J p)).comp (fderiv ℝ J p) := by
    convert fderiv_comp p hdF hJ using 1 <;> try with_reducible_and_instances rfl
    rfl
  rw [fderiv_clm_apply hc (differentiableAt_const (c := v)), hcomp]
  simp

theorem sixVariableP_second_vertical_direction
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ r ∈ U, covHessian g z r 1 1 ≠ 0) (hp : p ∈ U)
    (v : DarbouxState) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    iteratedFDeriv ℝ 2 (sixVariableP g) (solutionJet z p)
        ![coordPartial 1 (solutionJet z) p, v] =
      coordPartial 1 (heightPFirst g z 0) p * v 2 +
      coordPartial 1 (heightPFirst g z 1) p * v 3 +
      2 * coordPartial 1 (hessianQuotient g z) p * v 4 -
      coordPartial 1 (fun r => (hessianQuotient g z r)^2 +
        gaussianCurvature g r * darbouxG g z r) p * v 5 := by
  rw [second_fderiv_comp_constant_direction
    (sixVariableP_contDiffAt_solutionJet hg hU hp (hyy _ hp))
    (((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))]
  have heq : (fun r => fderiv ℝ (sixVariableP g) (solutionJet z r) v) =ᶠ[𝓝 p]
      (fun r => heightPFirst g z 0 r * v 2 + heightPFirst g z 1 r * v 3 +
        2 * hessianQuotient g z r * v 4 -
        ((hessianQuotient g z r)^2 + gaussianCurvature g r * darbouxG g z r) * v 5) := by
    filter_upwards [hU.mem_nhds hp] with r hr
    exact sixVariableP_vertical_direction hg hU hr (hyy _ hr) v hv0 hv1
  have h0 := ((heightPFirst_contDiffOn hg hU hz hyy 0).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have h1 := ((heightPFirst_contDiffOn hg hU hz hyy 1).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hq := ((hessianQuotient_contDiffOn hg hU hz hyy).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hK := ((gaussianCurvature_contDiffOn hg hU).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hG := ((darbouxG_contDiffOn hg hU hz hyy).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have ha : DifferentiableAt ℝ (fun r => (hessianQuotient g z r)^2 +
      gaussianCurvature g r * darbouxG g z r) p := (hq.pow 2).add (hK.mul hG)
  have hd := (((h0.hasFDerivAt.mul_const (v 2)).add
    (h1.hasFDerivAt.mul_const (v 3))).add
    ((hq.hasFDerivAt.const_mul 2).mul_const (v 4))).sub (ha.hasFDerivAt.mul_const (v 5))
  simp only [Pi.add_def, Pi.sub_def] at hd
  unfold coordPartial
  rw [heq.fderiv_eq]
  change fderiv ℝ (fun r => heightPFirst g z 0 r * v 2 + heightPFirst g z 1 r * v 3 +
      2 * hessianQuotient g z r * v 4 -
      ((hessianQuotient g z r)^2 + gaussianCurvature g r * darbouxG g z r) * v 5) p
      (Pi.single 1 1) = _
  rw [hd.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

def secondJetCorrection (g : MetricField) (z u : Coord → ℝ) (p : Coord) : ℝ :=
  2 * coordPartial 1 (hessianQuotient g z) p * coordPartial 0 u p -
  coordPartial 1 (fun r => (hessianQuotient g z r)^2 +
    gaussianCurvature g r * darbouxG g z r) p * coordPartial 1 u p

theorem actualP_pair_extract_secondJet
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hp : (![x, y] : Coord) ∈ U) (n : ℕ) (hn : 2 ≤ n) :
    chainTerm (sixVariableP g) (solutionJetCurve z x) (ChainWord.pair 1 n) y =
      secondJetCorrection g z (verticalJet z (n + 1)) ![x, y] +
        firstJetPairRemainder g z n ![x, y] := by
  have hfirst : iteratedDeriv 1 (solutionJetCurve z x) y =
      coordPartial 1 (solutionJet z) ![x, y] :=
    verticalJet_slice hU (solutionJet_contDiffOn hU hz) x 1 y hp
  rw [chainTerm_pair_eq, hfirst, solutionJetCurve_iteratedDeriv hU hz hp n hn]
  change iteratedFDeriv ℝ 2 (sixVariableP g) (solutionJet z ![x, y]) _ = _
  rw [sixVariableP_second_vertical_direction hg hU hz hyy hp _ (by rfl) (by rfl)]
  change
    coordPartial 1 (heightPFirst g z 0) ![x, y] * coordPartial 0 (verticalJet z n) ![x, y] +
    coordPartial 1 (heightPFirst g z 1) ![x, y] * coordPartial 1 (verticalJet z n) ![x, y] +
    2 * coordPartial 1 (hessianQuotient g z) ![x, y] *
      coordPartial 0 (coordPartial 1 (verticalJet z n)) ![x, y] -
    coordPartial 1 (fun r => (hessianQuotient g z r)^2 +
      gaussianCurvature g r * darbouxG g z r) ![x, y] *
      coordPartial 1 (coordPartial 1 (verticalJet z n)) ![x, y] = _
  unfold secondJetCorrection firstJetPairRemainder
  change _ =
    (2 * coordPartial 1 (hessianQuotient g z) ![x, y] *
        coordPartial 0 (coordPartial 1 (verticalJet z n)) ![x, y] -
      coordPartial 1 (fun r => (hessianQuotient g z r)^2 +
        gaussianCurvature g r * darbouxG g z r) ![x, y] *
        coordPartial 1 (coordPartial 1 (verticalJet z n)) ![x, y]) + _
  ring

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Sobolev

theorem capRectangle_isCompact (tl tr sb st : ℝ) : IsCompact (closedRectangle tl tr sb st) := by
  have he : closedRectangle tl tr sb st =
      (fun q : ℝ × ℝ => boxPoint q.1 q.2) '' (Icc tl tr ×ˢ Icc sb st) := by
    ext p
    constructor
    · intro hp
      exact ⟨(p 0,p 1),⟨hp.1,hp.2⟩,boxPoint_eta p⟩
    · rintro ⟨q,hq,rfl⟩
      exact boxPoint_mem hq.1 hq.2
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).image (by unfold boxPoint; fun_prop)

theorem rectangleIntegral_eq_coordinate_closed_area
    {tl tr sb st : ℝ} {F : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st F = ∫ p in closedRectangle tl tr sb st, F p := by
  rw [rectangleIntegral_eq_closed_area ht hs hF]
  have hh := (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.finTwoArrow (α := ℝ)).measurableEmbedding
    (fun q : ℝ × ℝ => F (boxPoint q.1 q.2)) (Icc tl tr ×ˢ Icc sb st)
  change (∫ p in closedRectangle tl tr sb st, F (boxPoint (p 0) (p 1))) =
    ∫ q in Icc tl tr ×ˢ Icc sb st, F (boxPoint q.1 q.2) at hh
  simpa only [boxPoint_eta] using hh.symm

theorem cap_image_integral_formula
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    {tl tr sb st : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st)) :
    (∫ p in capChart Y '' closedRectangle tl tr sb st, f p) =
      rectangleIntegral tl tr sb st (fun p => coordPartial 1 (capFlowHeight Y) p*capPullback Y f p) := by
  have hrect : MeasurableSet (closedRectangle tl tr sb st) := (capRectangle_isCompact _ _ _ _).isClosed.measurableSet
  have hchart := capChart_contDiffOn hYs
  have hd (p : Coord) (hp : p ∈ closedRectangle tl tr sb st) :
      HasFDerivWithinAt (capChart Y) (fderiv ℝ (capChart Y) p) (closedRectangle tl tr sb st) p :=
    ((hchart.contDiffAt (capChartDomain_isOpen.mem_nhds (hbox hp))).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hinj := (capChart_injOn_of_pairChart hsource heq).mono hbox
  have hcomp : ContinuousOn (capPullback Y f) (closedRectangle tl tr sb st) :=
    hf.comp (hchart.continuousOn.mono hbox) (fun p hp => ⟨p,hp,rfl⟩)
  have hJ : ContinuousOn (coordPartial 1 (capFlowHeight Y)) (closedRectangle tl tr sb st) :=
    (partial_contDiffOn (capFlowHeight_contDiffOn hYs) capChartDomain_isOpen 1).continuousOn.mono hbox
  calc
    _ = ∫ p in closedRectangle tl tr sb st, |(fderiv ℝ (capChart Y) p).det| • f (capChart Y p) :=
      integral_image_eq_integral_abs_det_fderiv_smul volume hrect hd hinj f
    _ = ∫ p in closedRectangle tl tr sb st, coordPartial 1 (capFlowHeight Y) p*capPullback Y f p := by
      apply setIntegral_congr_fun hrect
      intro p hp
      change |(fderiv ℝ (capChart Y) p).det| * f (capChart Y p) = _
      rw [capChart_abs_det_fderiv hYs hvar (hbox hp)]
      rfl
    _ = _ := (rectangleIntegral_eq_coordinate_closed_area ht hs (hJ.mul hcomp)).symm

theorem cap_rectangle_square_integral_bounds
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    {tl tr sb st M : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hJ : ∀ p ∈ closedRectangle tl tr sb st,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M))
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st)) :
    Real.exp (-2*M)*rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) ≤
      ∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2 ∧
    (∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2) ≤
      Real.exp (2*M)*rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) := by
  have hchart := capChart_contDiffOn hYs
  have hfc : ContinuousOn (fun p => (capPullback Y f p)^2) (closedRectangle tl tr sb st) :=
    (hf.comp (hchart.continuousOn.mono hbox) (fun p hp => ⟨p,hp,rfl⟩)).pow 2
  have hJc : ContinuousOn (coordPartial 1 (capFlowHeight Y)) (closedRectangle tl tr sb st) :=
    (partial_contDiffOn (capFlowHeight_contDiffOn hYs) capChartDomain_isOpen 1).continuousOn.mono hbox
  have hformula := cap_image_integral_formula hYs hvar hsource heq ht hs hbox (hf.pow 2)
  change (∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2) =
    rectangleIntegral tl tr sb st (fun p => coordPartial 1 (capFlowHeight Y) p*(capPullback Y f p)^2) at hformula
  rw [hformula]
  constructor
  · have hh := rectangleIntegral_mono ht hs (continuousOn_const.mul hfc) (hJc.mul hfc)
      (fun p hp => mul_le_mul_of_nonneg_right (hJ p hp).1 (sq_nonneg _))
    simpa only [Pi.mul_def, rectangleIntegral_const_mul] using hh
  · have hh := rectangleIntegral_mono ht hs (hJc.mul hfc) (continuousOn_const.mul hfc)
      (fun p hp => mul_le_mul_of_nonneg_right (hJ p hp).2 (sq_nonneg _))
    simpa only [Pi.mul_def, rectangleIntegral_const_mul] using hh

theorem cap_pullback_square_integral_le_image
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    {tl tr sb st M : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hJ : ∀ p ∈ closedRectangle tl tr sb st,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M))
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) ≤
      Real.exp (2*M)*(∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2) := by
  have hh := (cap_rectangle_square_integral_bounds hYs hvar hsource heq ht hs hbox hJ hf).1
  have hscale : Real.exp (2*M)*Real.exp (-2*M) = 1 := by rw [←Real.exp_add]; simp
  calc
    _ = Real.exp (2*M)*(Real.exp (-2*M)*rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2)) := by
      rw [←mul_assoc,hscale,one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem chainTerm_eq_coordinateChainTerm
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U)
    (w : ChainWord) :
    chainTerm (sixVariableP g) (solutionJetCurve z x) w y =
      coordinateChainTerm g z w ![x, y] := by
  apply congrArg (iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z ![x, y]))
  funext i
  exact verticalJet_slice hU (solutionJet_contDiffOn hU hz) x (w.order i) y hp

theorem chainSum_eq_coordinateChainSum
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U)
    (ws : List ChainWord) :
    chainSum (sixVariableP g) (solutionJetCurve z x) ws y =
      coordinateChainSum g z ws ![x, y] := by
  unfold chainSum coordinateChainSum
  congr 1
  apply List.map_congr_left
  intro word _
  exact chainTerm_eq_coordinateChainTerm hU hz hp word

theorem actualP_single_linearization
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : (![x, y] : Coord) ∈ U) (hyy : covHessian g z ![x, y] 1 1 ≠ 0)
    (n : ℕ) (hn : 2 ≤ n) :
    chainTerm (sixVariableP g) (solutionJetCurve z x) (ChainWord.single n) y =
      directLinearization g z (verticalJet z n) ![x, y] := by
  rw [chainTerm_single_eq]
  have h := fullBlockPartition_actual_linearization hg hU hz hp hyy n hn
  rw [fullBlockPartition_term] at h
  exact h

theorem actual_differentiated_Darboux
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hp : (![x, y] : Coord) ∈ U) (m : ℕ) :
    coordPartial 0 (coordPartial 0 (verticalJet z (m + 3))) ![x, y] =
      directLinearization g z (verticalJet z (m + 3)) ![x, y] +
        (m + 3 : ℝ) * secondJetCorrection g z (verticalJet z (m + 3)) ![x, y] +
        actualHighRemainder g z m ![x, y] := by
  have heq : (fun t => coordPartial 0 (coordPartial 0 z) ![x, t]) =ᶠ[𝓝 y]
      sixVariableP g ∘ solutionJetCurve z x := by
    filter_upwards [(hU.preimage (verticalPoint_contDiff x).continuous).mem_nhds hp] with t ht
    change coordPartial 0 (coordPartial 0 z) ![x, t] = sixVariableP g (solutionJet z ![x, t])
    rw [sixVariableP_solutionJet]
    exact solvedDarboux_at_height hg hU hz ht (hyy _ ht) (hD _ ht)
  have htop := actualP_top_chain_expansion hg hU hz hyy hp m
  rw [← heq.iteratedDeriv_eq (m + 3)] at htop
  rw [verticalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0)
      x (m + 3) y hp,
    verticalJet_two_coordPartials hU hz hp (m + 3) 0 0,
    actualP_single_linearization hg hU hz hp (hyy _ hp) (m + 3) (by omega),
    actualP_pair_extract_secondJet hg hU hz hyy hp (m + 2) (by omega),
    chainSum_eq_coordinateChainSum hU hz hp] at htop
  unfold actualHighRemainder
  convert htop using 1 <;> try with_reducible_and_instances rfl
  ring

theorem actual_differentiated_Darboux_at
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (m : ℕ) {p : Coord} (hp : p ∈ U) :
    coordPartial 0 (coordPartial 0 (verticalJet z (m + 3))) p =
      directLinearization g z (verticalJet z (m + 3)) p +
        (m + 3 : ℝ) * secondJetCorrection g z (verticalJet z (m + 3)) p +
        actualHighRemainder g z m p := by
  have he : (![p 0, p 1] : Coord) = p := by
    ext i
    fin_cases i <;> rfl
  simpa only [he] using actual_differentiated_Darboux hg hU hz hD hyy
    (x := p 0) (y := p 1) (by simpa only [he] using hp) m

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem cap_rectangle_density_integral_bounds
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    {tl tr sb st M : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hJ : ∀ p ∈ closedRectangle tl tr sb st,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M))
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st))
    (hf0 : ∀ p ∈ capChart Y '' closedRectangle tl tr sb st, 0 ≤ f p) :
    Real.exp (-2*M)*rectangleIntegral tl tr sb st (capPullback Y f) ≤
      (∫ p in capChart Y '' closedRectangle tl tr sb st, f p) ∧
    (∫ p in capChart Y '' closedRectangle tl tr sb st, f p) ≤
      Real.exp (2*M)*rectangleIntegral tl tr sb st (capPullback Y f) := by
  have hfc : ContinuousOn (capPullback Y f) (closedRectangle tl tr sb st) :=
    hf.comp ((capChart_contDiffOn hYs).continuousOn.mono hbox) (fun p hp => ⟨p,hp,rfl⟩)
  have hJc : ContinuousOn (coordPartial 1 (capFlowHeight Y)) (closedRectangle tl tr sb st) :=
    (partial_contDiffOn (capFlowHeight_contDiffOn hYs) capChartDomain_isOpen 1).continuousOn.mono hbox
  rw [cap_image_integral_formula hYs hvar hsource heq ht hs hbox hf]
  constructor
  · have hh := rectangleIntegral_mono ht hs (continuousOn_const.mul hfc) (hJc.mul hfc)
      (fun p hp => mul_le_mul_of_nonneg_right (hJ p hp).1 (hf0 _ ⟨p,hp,rfl⟩))
    simpa only [Pi.mul_def, rectangleIntegral_const_mul] using hh
  · have hh := rectangleIntegral_mono ht hs (hJc.mul hfc) (continuousOn_const.mul hfc)
      (fun p hp => mul_le_mul_of_nonneg_right (hJ p hp).2 (hf0 _ ⟨p,hp,rfl⟩))
    simpa only [Pi.mul_def, rectangleIntegral_const_mul] using hh

theorem cap_pullback_density_integral_le_image
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    {tl tr sb st M : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hJ : ∀ p ∈ closedRectangle tl tr sb st,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M))
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st))
    (hf0 : ∀ p ∈ capChart Y '' closedRectangle tl tr sb st, 0 ≤ f p) :
    rectangleIntegral tl tr sb st (capPullback Y f) ≤
      Real.exp (2*M)*(∫ p in capChart Y '' closedRectangle tl tr sb st, f p) := by
  have hh := (cap_rectangle_density_integral_bounds hYs hvar hsource heq ht hs hbox hJ hf hf0).1
  have hscale : Real.exp (2*M)*Real.exp (-2*M) = 1 := by
    rw [←Real.exp_add,show 2*M+(-2*M) = 0 by ring,Real.exp_zero]
  calc
    _ = Real.exp (2*M)*(Real.exp (-2*M)*rectangleIntegral tl tr sb st (capPullback Y f)) := by
      rw [←mul_assoc,hscale,one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Weighted

theorem actual_differentiated_drift
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (m : ℕ) {p : Coord} (hp : p ∈ U) :
    driftOperator (hessianQuotient g z) (heightOriginalA g z)
      (heightOriginalB g z (m + 3)) (heightOriginalC0 g z (m + 3))
      (verticalJet z (m + 3)) p = actualHighRemainder g z m p := by
  have hid := driftOperator_linearized_identity
    (hessianQuotient_contDiffOn hg hU hz hyy) (verticalJet_contDiffOn hU hz (m + 3))
    (heightOriginalA_contDiffOn hg hU hz hyy) hU hp
    (heightPFirst g z 0) (heightPFirst g z 1) (m + 3)
  have hC : (fun r => coordinateDrift (hessianQuotient g z) (hessianQuotient g z) r -
      heightPFirst g z 0 r * hessianQuotient g z r - heightPFirst g z 1 r +
      (m + 3 : ℝ) * coordPartial 1 (heightOriginalA g z) r) =
      heightOriginalC0 g z (m + 3) := by
    funext r
    simp only [heightOriginalC0, Nat.cast_add, Nat.cast_ofNat]
    ring
  simp only [Nat.cast_add, Nat.cast_ofNat] at hid
  rw [hC] at hid
  have hB : (fun r => -heightPFirst g z 0 r -
      2 * (m + 3 : ℝ) * coordPartial 1 (hessianQuotient g z) r) =
      heightOriginalB g z (m + 3) := by
    funext r
    simp only [heightOriginalB, Nat.cast_add, Nat.cast_ofNat]
  rw [hB] at hid
  rw [hid]
  have h := actual_differentiated_Darboux_at hg hU hz hD hyy m hp
  unfold directLinearization secondJetCorrection at h
  simp only [heightOriginalA] at *
  linarith only [h]

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def coordinateGradientSquare (f : Coord → ℝ) (p : Coord) : ℝ :=
  (coordPartial 0 f p)^2+(coordPartial 1 f p)^2

theorem coordinateGradientSquare_nonneg (f : Coord → ℝ) (p : Coord) :
    0 ≤ coordinateGradientSquare f p := add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem coordinateGradientSquare_contDiffOn {f : Coord → ℝ} {V : Set Coord}
    (hf : ContDiffOn ℝ ∞ f V) (hV : IsOpen V) :
    ContDiffOn ℝ ∞ (coordinateGradientSquare f) V :=
  ((partial_contDiffOn hf hV 0).pow 2).add ((partial_contDiffOn hf hV 1).pow 2)

theorem triangular_gradient_forward_scalar {a b H x y : ℝ}
    (ha : |a| ≤ 1) (hb : 0 ≤ b) (hbH : b ≤ H) :
    (x+a*y)^2+(b*y)^2 ≤ (2+H^2)*(x^2+y^2) := by
  have hH : 0 ≤ H := hb.trans hbH
  have ha2 : a^2 ≤ 1 := (sq_le_one_iff_abs_le_one a).2 ha
  have hb2 : b^2 ≤ H^2 := (sq_le_sq₀ hb hH).2 hbH
  have hay := mul_le_mul_of_nonneg_right ha2 (sq_nonneg y)
  have hby := mul_le_mul_of_nonneg_right hb2 (sq_nonneg y)
  have hsum : (x+a*y)^2 ≤ 2*(x^2+(a*y)^2) := add_sq_le
  have hx := mul_nonneg (sq_nonneg H) (sq_nonneg x)
  nlinarith only [hay,hby,hsum,hx]

theorem triangular_gradient_inverse_scalar {a b H x y : ℝ}
    (ha : |a| ≤ 1) (hH : 0 < H) (hb : 1/H ≤ b) :
    x^2+y^2 ≤ (2+3*H^2)*((x+a*y)^2+(b*y)^2) := by
  have ha2 : a^2 ≤ 1 := (sq_le_one_iff_abs_le_one a).2 ha
  have hHb : 1 ≤ b*H := (div_le_iff₀ hH).1 hb
  have hHb2 : 1 ≤ (b*H)^2 := by
    simpa only [one_pow] using (sq_le_sq₀ (show (0:ℝ) ≤ 1 by norm_num) (by linarith : 0 ≤ b*H)).2 hHb
  have hy := mul_le_mul_of_nonneg_right hHb2 (sq_nonneg y)
  have hay := mul_le_mul_of_nonneg_right ha2 (sq_nonneg y)
  have hx : ((x+a*y)+(-a*y))^2 ≤ 2*((x+a*y)^2+(-a*y)^2) := add_sq_le
  have hgap : 0 ≤ 3*H^2*(x+a*y)^2+2*(b*y)^2 := by positivity
  nlinarith only [hy,hay,hx,hgap]

theorem capPullback_gradient_pointwise
    {Y : ℝ → ℝ → ℝ} {q f : Coord → ℝ} {M : ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {p : Coord} (hp : p ∈ capChartDomain)
    (hf : DifferentiableAt ℝ f (capChart Y p))
    (hq : |q (capChart Y p)| ≤ 1)
    (hJ : Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
      coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M)) :
    coordinateGradientSquare (capPullback Y f) p ≤
      (2+(Real.exp (2*M))^2)*capPullback Y (coordinateGradientSquare f) p ∧
    capPullback Y (coordinateGradientSquare f) p ≤
      (2+3*(Real.exp (2*M))^2)*coordinateGradientSquare (capPullback Y f) p := by
  have hJpos : 0 < coordPartial 1 (capFlowHeight Y) p := (Real.exp_pos _).trans_le hJ.1
  have hJinv : 1/Real.exp (2*M) ≤ coordPartial 1 (capFlowHeight Y) p := by
    simpa only [show -2*M = -(2*M) by ring,Real.exp_neg,one_div] using hJ.1
  have htime := capPullback_partial_time hYs hode hp hf
  have hinit := capPullback_partial_initial hYs hp hf
  change (coordPartial 0 (capPullback Y f) p)^2+(coordPartial 1 (capPullback Y f) p)^2 ≤
      (2+(Real.exp (2*M))^2)*((coordPartial 0 f (capChart Y p))^2+(coordPartial 1 f (capChart Y p))^2) ∧
    (coordPartial 0 f (capChart Y p))^2+(coordPartial 1 f (capChart Y p))^2 ≤
      (2+3*(Real.exp (2*M))^2)*((coordPartial 0 (capPullback Y f) p)^2+(coordPartial 1 (capPullback Y f) p)^2)
  rw [htime,hinit]
  simp only [coordinateDrift,capPullback]
  have ha : |-q (capChart Y p)| ≤ 1 := by simpa only [abs_neg] using hq
  constructor
  · simpa only [neg_mul,sub_eq_add_neg,mul_comm] using
      triangular_gradient_forward_scalar (x := coordPartial 0 f (capChart Y p))
        (y := coordPartial 1 f (capChart Y p)) ha hJpos.le hJ.2
  · simpa only [neg_mul,sub_eq_add_neg,mul_comm] using
      triangular_gradient_inverse_scalar (x := coordPartial 0 f (capChart Y p))
        (y := coordPartial 1 f (capChart Y p)) ha (Real.exp_pos _) hJinv

theorem cap_gradient_integral_bounds
    {Y : ℝ → ℝ → ℝ} {q f : Coord → ℝ} {V : Set Coord}
    {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    (hf : ContDiffOn ℝ ∞ f V) (hV : IsOpen V)
    (hmap : MapsTo (capChart Y) capChartDomain V)
    {tl tr sb st M : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hq : ∀ p ∈ closedRectangle tl tr sb st, |q (capChart Y p)| ≤ 1)
    (hJ : ∀ p ∈ closedRectangle tl tr sb st,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M)) :
    rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y f)) ≤
      ((2+(Real.exp (2*M))^2)*Real.exp (2*M))*
        (∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare f p) ∧
    (∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare f p) ≤
      (Real.exp (2*M)*(2+3*(Real.exp (2*M))^2))*
        rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y f)) := by
  have hGp := coordinateGradientSquare_contDiffOn hf hV
  have hGc : ContinuousOn (coordinateGradientSquare f) (capChart Y '' closedRectangle tl tr sb st) :=
    hGp.continuousOn.mono (by rintro _ ⟨p,hp,rfl⟩; exact hmap (hbox hp))
  have hP : ContDiffOn ℝ ∞ (capPullback Y f) capChartDomain := capPullback_contDiffOn hYs hf hmap
  have hGPc : ContinuousOn (coordinateGradientSquare (capPullback Y f)) (closedRectangle tl tr sb st) :=
    (coordinateGradientSquare_contDiffOn hP capChartDomain_isOpen).continuousOn.mono hbox
  have hPGc : ContinuousOn (capPullback Y (coordinateGradientSquare f)) (closedRectangle tl tr sb st) :=
    (capPullback_contDiffOn hYs hGp hmap).continuousOn.mono hbox
  have hpoint (p : Coord) (hp : p ∈ closedRectangle tl tr sb st) :=
    capPullback_gradient_pointwise hYs hode (hbox hp)
      ((hf.contDiffAt (hV.mem_nhds (hmap (hbox hp)))).differentiableAt (by simp)) (hq p hp) (hJ p hp)
  have hzero := fun p (_hp : p ∈ capChart Y '' closedRectangle tl tr sb st) =>
    coordinateGradientSquare_nonneg f p
  have hforward := rectangleIntegral_mono ht hs hGPc (continuousOn_const.mul hPGc)
    (fun p hp => (hpoint p hp).1)
  simp only [Pi.mul_def, rectangleIntegral_const_mul] at hforward
  have hinverse := rectangleIntegral_mono ht hs hPGc (continuousOn_const.mul hGPc)
    (fun p hp => (hpoint p hp).2)
  simp only [Pi.mul_def, rectangleIntegral_const_mul] at hinverse
  have hlower := cap_pullback_density_integral_le_image hYs hvar hsource heq ht hs hbox hJ hGc hzero
  have hupper := (cap_rectangle_density_integral_bounds hYs hvar hsource heq ht hs hbox hJ hGc hzero).2
  constructor
  · calc
      _ ≤ (2+(Real.exp (2*M))^2)*rectangleIntegral tl tr sb st
          (capPullback Y (coordinateGradientSquare f)) := hforward
      _ ≤ (2+(Real.exp (2*M))^2)*(Real.exp (2*M)*
          (∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare f p)) :=
        mul_le_mul_of_nonneg_left hlower (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ Real.exp (2*M)*rectangleIntegral tl tr sb st
          (capPullback Y (coordinateGradientSquare f)) := hupper
      _ ≤ Real.exp (2*M)*((2+3*(Real.exp (2*M))^2)*
          rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y f))) :=
        mul_le_mul_of_nonneg_left hinverse (Real.exp_pos _).le
      _ = _ := by ring

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted

theorem actual_flow_high_equation
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t)))
        (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (m : ℕ) {p : Coord}
    (hp : p ∈ capChartDomain) :
    multiplierOperator (heightChartA g z Y) (heightChartB g z Y (m + 3))
      (heightChartC g z Y (m + 3)) (capPullback Y (verticalJet z (m + 3))) p =
      capPullback Y (actualHighRemainder g z m) p := by
  rw [← height_coefficient_operator_transport hg hU hz hyy hY hode hvar hmap
    (verticalJet_contDiffOn hU hz (m + 3)) hp (m + 3)]
  exact actual_differentiated_drift hg hU hz hD hyy m (hmap hp)

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

theorem capOuterRectangle_subset_domain {L R A b : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (hb : b < 2) :
    closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A) b ⊆ capChartDomain := by
  obtain ⟨hlo,hli,hlu,hri,hrr,hro,hao,hai,hau,hlx,hrx⟩ := capOuterRectangle_edges hL hR hA
  intro p hp
  exact ⟨⟨hlo.trans_le hp.1.1, hp.1.2.trans_lt hro⟩,
    ⟨hao.trans_le hp.2.1,hp.2.2.trans_lt hb⟩⟩

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry

theorem heightOriginalC0_contDiffOn {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightOriginalC0 g z ell) U := by
  have hq := hessianQuotient_contDiffOn hg hU hz hyy
  exact (((coordinateDrift_contDiffOn hq hq hU).sub
    (hq.mul (heightPFirst_contDiffOn hg hU hz hyy 0))).sub
      (heightPFirst_contDiffOn hg hU hz hyy 1)).add
        (contDiffOn_const.mul (partial_contDiffOn (heightOriginalA_contDiffOn hg hU hz hyy) hU 1))

theorem driftOperator_contDiffOn {q A B C u : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U) (hA : ContDiffOn ℝ ∞ A U)
    (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (driftOperator q A B C u) U := by
  have hDu := coordinateDrift_contDiffOn hq hu hU
  exact (((coordinateDrift_contDiffOn hq hDu hU).add
    (hA.mul (partial_contDiffOn (partial_contDiffOn hu hU 1) hU 1))).add
      (hB.mul hDu)).add (hC.mul (partial_contDiffOn hu hU 1))

end SmoothLocal.Flow

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow

theorem actualHighRemainder_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (m : ℕ) :
    ContDiffOn ℝ ∞ (actualHighRemainder g z m) U := by
  have hh := driftOperator_contDiffOn hU (hessianQuotient_contDiffOn hg hU hz hyy)
    (heightOriginalA_contDiffOn hg hU hz hyy) (heightOriginalB_contDiffOn hg hU hz hyy (m+3))
    (heightOriginalC0_contDiffOn hg hU hz hyy (m+3)) (verticalJet_contDiffOn hU hz (m+3))
  exact hh.congr (fun p hp => (actual_differentiated_drift hg hU hz hD hyy m hp).symm)

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem heightPhysicalCapConstant_pos (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) : 0 < heightPhysicalCapConstant G Z d c e0 kappa ell L R bottom top b := by
  unfold heightPhysicalCapConstant
  positivity

theorem heightUniformCapEstimateRHS_eq_factors (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) (u f : Coord → ℝ) :
    heightUniformCapEstimateRHS G Z d c e0 kappa ell L R bottom top b u f =
      (heightCapIntegralFactors G Z d c e0 kappa ell L R bottom top b).1*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (f p)^2)+
      (heightCapIntegralFactors G Z d c e0 kappa ell L R bottom top b).2*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (u p)^2) := by
  unfold heightUniformCapEstimateRHS heightCapIntegralFactors
  ring

theorem scalar_two_integral_transport
    {a b H J F U Fp Up P Q : ℝ} (hH : 0 ≤ H) (hJ : 0 ≤ J)
    (hF : 0 ≤ F) (hU : 0 ≤ U) (hFp : 0 ≤ Fp) (hUp : 0 ≤ Up)
    (hFle : F ≤ H*Fp) (hUle : U ≤ H*Up)
    (hP : P ≤ a*F+b*U) (hQ : Q ≤ J*P) :
    Q ≤ J*H*(|a|+|b|+1)*(Fp+Up) := by
  have habs : a*F+b*U ≤ |a| *F+|b| *U :=
    add_le_add (mul_le_mul_of_nonneg_right (le_abs_self a) hF)
      (mul_le_mul_of_nonneg_right (le_abs_self b) hU)
  have harea : |a| *F+|b| *U ≤ H*(|a| *Fp+|b| *Up) := by
    calc
      _ ≤ |a| *(H*Fp)+|b| *(H*Up) :=
        add_le_add (mul_le_mul_of_nonneg_left hFle (abs_nonneg a))
          (mul_le_mul_of_nonneg_left hUle (abs_nonneg b))
      _ = _ := by ring
  have hsum : |a| *Fp+|b| *Up ≤ (|a|+|b|+1)*(Fp+Up) := by
    have h1 := mul_nonneg (abs_nonneg a) hUp
    have h2 := mul_nonneg (abs_nonneg b) hFp
    nlinarith only [h1,h2,hFp,hUp]
  calc
    Q ≤ J*P := hQ
    _ ≤ J*(a*F+b*U) := mul_le_mul_of_nonneg_left hP hJ
    _ ≤ J*(|a| *F+|b| *U) := mul_le_mul_of_nonneg_left habs hJ
    _ ≤ J*(H*(|a| *Fp+|b| *Up)) := mul_le_mul_of_nonneg_left harea hJ
    _ ≤ J*(H*((|a|+|b|+1)*(Fp+Up))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hH) hJ
    _ = _ := by ring

theorem cap_gradient_estimate_to_physical_images
    {Y : ℝ → ℝ → ℝ} {q u f : Coord → ℝ} {V : Set Coord}
    {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2:ℝ) 2, ∀ t ∈ Ioo (-2:ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hode : ∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2:ℝ) 2) t)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    (hu : ContDiffOn ℝ ∞ u V) (hV : IsOpen V)
    (hmap : MapsTo (capChart Y) capChartDomain V)
    {tl tr sb st TL TR SB ST M a b : ℝ}
    (ht : tl ≤ tr) (hs : sb ≤ st) (hT : TL ≤ TR) (hS : SB ≤ ST)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hBOX : closedRectangle TL TR SB ST ⊆ capChartDomain)
    (hq : ∀ p ∈ capChartDomain, |q (capChart Y p)| ≤ 1)
    (hJ : ∀ p ∈ capChartDomain,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M))
    (hf : ContinuousOn f (capChart Y '' closedRectangle TL TR SB ST))
    (hestimate : rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y u)) ≤
      a*rectangleIntegral TL TR SB ST (fun p => (capPullback Y f p)^2)+
        b*rectangleIntegral TL TR SB ST (fun p => (capPullback Y u p)^2)) :
    (∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare u p) ≤
      (Real.exp (2*M)*(2+3*(Real.exp (2*M))^2))*Real.exp (2*M)*(|a|+|b|+1)*
        ((∫ p in capChart Y '' closedRectangle TL TR SB ST, (f p)^2)+
          (∫ p in capChart Y '' closedRectangle TL TR SB ST, (u p)^2)) := by
  have huI : ContinuousOn u (capChart Y '' closedRectangle TL TR SB ST) :=
    hu.continuousOn.mono (by rintro _ ⟨p,hp,rfl⟩; exact hmap (hBOX hp))
  have hfc : ContinuousOn (capPullback Y f) (closedRectangle TL TR SB ST) :=
    hf.comp ((capChart_contDiffOn hYs).continuousOn.mono hBOX) (fun p hp => ⟨p,hp,rfl⟩)
  have huc : ContinuousOn (capPullback Y u) (closedRectangle TL TR SB ST) :=
    (capPullback_contDiffOn hYs hu hmap).continuousOn.mono hBOX
  have hF : 0 ≤ rectangleIntegral TL TR SB ST (fun p => (capPullback Y f p)^2) := by
    have he := rectangleIntegral_eq_coordinate_closed_area hT hS (hfc.pow 2)
    change rectangleIntegral TL TR SB ST (fun p => (capPullback Y f p)^2) = _ at he
    rw [he]
    exact integral_nonneg (fun p => sq_nonneg _)
  have hU : 0 ≤ rectangleIntegral TL TR SB ST (fun p => (capPullback Y u p)^2) := by
    have he := rectangleIntegral_eq_coordinate_closed_area hT hS (huc.pow 2)
    change rectangleIntegral TL TR SB ST (fun p => (capPullback Y u p)^2) = _ at he
    rw [he]
    exact integral_nonneg (fun p => sq_nonneg _)
  have hFarea := cap_pullback_square_integral_le_image hYs hvar hsource heq hT hS hBOX
    (fun p hp => hJ p (hBOX hp)) hf
  have hUarea := cap_pullback_square_integral_le_image hYs hvar hsource heq hT hS hBOX
    (fun p hp => hJ p (hBOX hp)) huI
  have hGrad := (cap_gradient_integral_bounds hYs hvar hode hsource heq hu hV hmap ht hs hbox
    (fun p hp => hq p (hbox hp)) (fun p hp => hJ p (hbox hp))).2
  exact scalar_two_integral_transport (Real.exp_pos _).le (by positivity) hF hU
    (integral_nonneg (fun p => sq_nonneg (f p))) (integral_nonneg (fun p => sq_nonneg (u p)))
    hFarea hUarea hestimate hGrad

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model SmoothLocal.HighEquation

theorem exists_C8_one_flow_all_high_cap_estimates
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => (g0+eta) q i j) p‖ ≤ G)
    (hzB : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian (g0+eta) z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0+eta) z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0+eta) z p| ≤ (1:ℝ)/100)
    (hD : ∀ p ∈ modelSquare,
      (covHessian (g0+eta) z p).det = gaussianCurvature (g0+eta) p*heightEnergy (g0+eta) z p)
    (hk : 0 < kappa)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) :
    ∃ (V : Set Coord) (Y : ℝ → ℝ → ℝ),
      IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ (hessianQuotient (g0+eta) z) V ∧
      CoordinateBound (hessianQuotient (g0+eta) z) modelSquare 3 (heightQuotientJetBound G Z d c) ∧
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      ContinuousOn (uncurry Y) (Icc (-2:ℝ) 2 ×ˢ Icc (-2:ℝ) 2) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Ioo (-2:ℝ) 2, ∀ t ∈ Ioo (-2:ℝ) 2, 0 < deriv (fun r => Y r t) s) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient (g0+eta) z (coordinatePoint t (Y s t)))
          (Icc (-2:ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2, Y s t ∈ Icc (-3:ℝ) 3) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2, |Y s t-s| ≤ (1:ℝ)/50) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50) ∧
      ∀ m : ℕ,
        let epsilon := heightDirectedEpsilon G Z d c e0 kappa (m+3)
        let lambda := heightDirectedLambda G Z d c e0 kappa (m+3)
        let c1 := heightDirectedSlope G Z d c e0 kappa (m+3)
        let c2 := heightDirectedCoercivity G Z d c e0 kappa (m+3)
        0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧ 0 < c2 ∧
        (∀ p ∈ capChartDomain,
          multiplierOperator (heightChartA (g0+eta) z Y) (heightChartB (g0+eta) z Y (m+3))
            (heightChartC (g0+eta) z Y (m+3)) (capPullback Y (verticalJet z (m+3))) p =
              capPullback Y (actualHighRemainder (g0+eta) z m) p) ∧
        ∀ L R bottom top b : ℝ,
          -2 < L → R < 2 → -2 < bottom → L ≤ R → bottom ≤ top → top < b → b ≤ 0 →
          rectangleIntegral L R bottom top
            (fun p => (coordPartial 0 (capPullback Y (verticalJet z (m+3))) p)^2+
              (coordPartial 1 (capPullback Y (verticalJet z (m+3))) p)^2) ≤
            heightUniformCapEstimateRHS G Z d c e0 kappa (m+3) L R bottom top b
              (capPullback Y (verticalJet z (m+3)))
              (capPullback Y (actualHighRemainder (g0+eta) z m)) := by
  have hg4 (i j : Fin 2) : CoordinateBound (fun p => (g0+eta) p i j) modelSquare 4 G :=
    (coordinateBound_of_frechet_bounds (hg.1 i j) hU hSU (hgB i j)).mono (by norm_num) le_rfl
  have hz5 : CoordinateBound z modelSquare 5 Z := coordinateBound_five_of_frechet_eight hz hU hSU hzB
  obtain ⟨V,hV,hSV,hVU,_,hq,hqB⟩ :=
    exists_open_quotient_domain_with_closed_low_bounds hg hU hSU hz hG hZ hd hc hg4 hz5 hdet hyy
  obtain ⟨Y,hY,_,hstart,hode,_,hdisp50,hrange,_⟩ := exists_cap_flow hq hV hSV hsmall
  have hconf (s : ℝ) (hs : s ∈ Icc (-2:ℝ) 2) (t : ℝ) (ht : t ∈ Icc (-2:ℝ) 2) :
      Y s t ∈ Icc (-3:ℝ) 3 := abs_le.mp ((hrange s hs t ht).1.trans (by norm_num))
  have hYs := cap_flow_joint_contDiffOn hq hV hSV hY hconf hstart hode
  have hchart := capChart_contDiffOn hYs
  have hvar : ∀ s ∈ Ioo (-2:ℝ) 2, ∀ t ∈ Ioo (-2:ℝ) 2, 0 < deriv (fun r => Y r t) s :=
    fun s hs t ht => cap_flow_initial_deriv_pos hq hV hSV hY hconf hstart hode hs ht
  have hdisp (p : Coord) (hp : p ∈ capChartDomain) : |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50 :=
    hdisp50 (p 1) ⟨hp.2.1.le,hp.2.2.le⟩ (p 0) ⟨hp.1.1.le,hp.1.2.le⟩
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn (g0+eta) modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp p hp)
  have hyyO : ∀ p ∈ modelOpenSquare, covHessian (g0+eta) z p 1 1 ≠ 0 :=
    fun p hp => LowQuotient.denominator_ne_zero hc hyy p (modelOpenSquare_subset hp)
  have hPDE (m : ℕ) (p : Coord) (hp : p ∈ capChartDomain) :
      multiplierOperator (heightChartA (g0+eta) z Y) (heightChartB (g0+eta) z Y (m+3))
        (heightChartC (g0+eta) z Y (m+3)) (capPullback Y (verticalJet z (m+3))) p =
          capPullback Y (actualHighRemainder (g0+eta) z m) p :=
    actual_flow_high_equation hgO modelOpenSquare_isOpen hzO
      (fun p hp => hD p (modelOpenSquare_subset hp)) hyyO hYs hode hvar hmapO m hp
  refine ⟨V,Y,hV,hSV,hVU,hq,hqB,hchart,hY,hYs,hvar,hstart,hode,hconf,hdisp50,hdisp,?_⟩
  intro m
  obtain ⟨Ym,heps,heps1,hlambda,hc1,hc2,_,hstartm,hodem,hdispm,_,hestimatem⟩ :=
    exists_uniform_original_data_actual_high_cap_estimate hg hU hSU hz hG hZ hd hc he0 hg4 hz5
      hdet hyy hEfloor hsmall hD hk hbackground hsupport hcentral m
  have heq := capChart_eqOn_of_same_ode hq hV hSV hstart hode hdisp hstartm hodem hdispm
  refine ⟨heps,heps1,hlambda,hc1,hc2,hPDE m,?_⟩
  intro L R bottom top b hL hR hbottom hLR hbt htop hb
  have hT : closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b ⊆ capChartDomain :=
    capOuterRectangle_subset_domain hL hR hbottom (by linarith)
  have hS : closedRectangle L R bottom top ⊆ capChartDomain := by
    intro p hp
    exact ⟨⟨hL.trans_le hp.1.1,hp.1.2.trans_lt hR⟩,
      ⟨hbottom.trans_le hp.2.1,by linarith [hp.2.2]⟩⟩
  obtain ⟨hlo,hli,hlu,hri,hrr,hro,hao,hai,hau,hlx,hrx⟩ := capOuterRectangle_edges hL hR hbottom
  have hOT : capOuterLeft L ≤ capOuterRight R := by linarith
  have hOS : capOuterBottom bottom ≤ b := by linarith
  have huint := capPullback_square_rectangle_eq_of_chart_eqOn heq (verticalJet z (m+3)) hOT hOS hT
  have hfint := capPullback_square_rectangle_eq_of_chart_eqOn heq (actualHighRemainder (g0+eta) z m) hOT hOS hT
  have hRHS : heightUniformCapEstimateRHS G Z d c e0 kappa (m+3) L R bottom top b
      (capPullback Y (verticalJet z (m+3))) (capPullback Y (actualHighRemainder (g0+eta) z m)) =
      heightUniformCapEstimateRHS G Z d c e0 kappa (m+3) L R bottom top b
        (capPullback Ym (verticalJet z (m+3))) (capPullback Ym (actualHighRemainder (g0+eta) z m)) := by
    unfold heightUniformCapEstimateRHS
    rw [huint,hfint]
  rw [capPullback_gradient_rectangle_eq_of_chart_eqOn heq (verticalJet z (m+3)) hLR hbt hS,hRHS]
  exact hestimatem L R bottom top b hL hR hbottom hLR hbt htop hb

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model SmoothLocal.HighEquation

theorem cap_closed_image_properties {Y : ℝ → ℝ → ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50)
    {tl tr sb st : ℝ} (hbox : closedRectangle tl tr sb st ⊆ capChartDomain) :
    IsCompact (capChart Y '' closedRectangle tl tr sb st) ∧
    MeasurableSet (capChart Y '' closedRectangle tl tr sb st) ∧
    volume (capChart Y '' closedRectangle tl tr sb st) < ⊤ ∧
    capChart Y '' closedRectangle tl tr sb st ⊆ modelOpenSquare := by
  have hc : IsCompact (capChart Y '' closedRectangle tl tr sb st) :=
    (capRectangle_isCompact _ _ _ _).image_of_continuousOn
      ((capChart_contDiffOn hYs).continuousOn.mono hbox)
  refine ⟨hc,hc.measurableSet,hc.measure_lt_top,?_⟩
  rintro _ ⟨p,hp,rfl⟩
  exact capChart_mem_modelOpenSquare (hbox hp) (hdisp p (hbox hp))

theorem exists_C8_one_flow_physical_cap_estimates
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => (g0+eta) q i j) p‖ ≤ G)
    (hzB : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian (g0+eta) z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0+eta) z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0+eta) z p| ≤ (1:ℝ)/100)
    (hD : ∀ p ∈ modelSquare,
      (covHessian (g0+eta) z p).det = gaussianCurvature (g0+eta) p*heightEnergy (g0+eta) z p)
    (hk : 0 < kappa)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) :
    ∃ (V : Set Coord) (Y : ℝ → ℝ → ℝ),
      IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ (hessianQuotient (g0+eta) z) V ∧
      CoordinateBound (hessianQuotient (g0+eta) z) modelSquare 3 (heightQuotientJetBound G Z d c) ∧
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      ContinuousOn (uncurry Y) (Icc (-2:ℝ) 2 ×ˢ Icc (-2:ℝ) 2) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Ioo (-2:ℝ) 2, ∀ t ∈ Ioo (-2:ℝ) 2, 0 < deriv (fun r => Y r t) s) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient (g0+eta) z (coordinatePoint t (Y s t)))
          (Icc (-2:ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2, Y s t ∈ Icc (-3:ℝ) 3) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2, |Y s t-s| ≤ (1:ℝ)/50) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50) ∧
      (∀ tl tr sb st : ℝ, closedRectangle tl tr sb st ⊆ capChartDomain →
        IsCompact (capChart Y '' closedRectangle tl tr sb st) ∧
        MeasurableSet (capChart Y '' closedRectangle tl tr sb st) ∧
        volume (capChart Y '' closedRectangle tl tr sb st) < ⊤ ∧
        capChart Y '' closedRectangle tl tr sb st ⊆ modelOpenSquare) ∧
      ∀ m : ℕ,
        (∀ p ∈ capChartDomain,
          multiplierOperator (heightChartA (g0+eta) z Y) (heightChartB (g0+eta) z Y (m+3))
            (heightChartC (g0+eta) z Y (m+3)) (capPullback Y (verticalJet z (m+3))) p =
              capPullback Y (actualHighRemainder (g0+eta) z m) p) ∧
        ∀ L R bottom top b : ℝ,
          -2 < L → R < 2 → -2 < bottom → L ≤ R → bottom ≤ top → top < b → b ≤ 0 →
          0 < heightPhysicalCapConstant G Z d c e0 kappa (m+3) L R bottom top b ∧
          (∫ p in capChart Y '' closedRectangle L R bottom top,
            (coordPartial 0 (verticalJet z (m+3)) p)^2+(verticalJet z (m+4) p)^2) ≤
            heightPhysicalCapConstant G Z d c e0 kappa (m+3) L R bottom top b*
              ((∫ p in capChart Y '' closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b,
                  (actualHighRemainder (g0+eta) z m p)^2)+
                (∫ p in capChart Y '' closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b,
                  (verticalJet z (m+3) p)^2)) := by
  obtain ⟨V,Y,hV,hSV,hVU,hq,hqB,hchart,hY,hYs,hvar,hstart,hode,hconf,hdisp50,hdisp,hall⟩ :=
    exists_C8_one_flow_all_high_cap_estimates hg hU hSU hz hG hZ hd hc he0 hgB hzB hdet hyy hEfloor
      hsmall hD hk hbackground hsupport hcentral
  obtain ⟨_,hsource,_,heq,_,_⟩ :=
    exists_global_triangularFlow_chart hq hV hSV hY hconf hstart hode
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  have hMq (p : Coord) (hp : p ∈ modelSquare) :
      |coordPartial 1 (hessianQuotient (g0+eta) z) p| ≤ M := hqB [1] (by norm_num) p hp
  have hJ (p : Coord) (hp : p ∈ capChartDomain) :=
    capChart_jacobian_bounds hq hV hSV hY hconf hstart hode hM hMq hp
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn (g0+eta) modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp p hp)
  have hyyO : ∀ p ∈ modelOpenSquare, covHessian (g0+eta) z p 1 1 ≠ 0 :=
    fun p hp => LowQuotient.denominator_ne_zero hc hyy p (modelOpenSquare_subset hp)
  have hsmall1 (p : Coord) (hp : p ∈ capChartDomain) :
      |hessianQuotient (g0+eta) z (capChart Y p)| ≤ 1 :=
    (hsmall _ (modelOpenSquare_subset (hmapO hp))).trans (by norm_num)
  refine ⟨V,Y,hV,hSV,hVU,hq,hqB,hchart,hY,hYs,hvar,hstart,hode,hconf,hdisp50,hdisp,
    (fun tl tr sb st hbox => cap_closed_image_properties hYs hdisp hbox),?_⟩
  intro m
  obtain ⟨_,_,_,_,_,hPDE,hestimate⟩ := hall m
  refine ⟨hPDE,?_⟩
  intro L R bottom top b hL hR hbottom hLR hbt htop hb
  have hT : closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b ⊆ capChartDomain :=
    capOuterRectangle_subset_domain hL hR hbottom (by linarith)
  have hS : closedRectangle L R bottom top ⊆ capChartDomain := by
    intro p hp
    exact ⟨⟨hL.trans_le hp.1.1,hp.1.2.trans_lt hR⟩,
      ⟨hbottom.trans_le hp.2.1,by linarith [hp.2.2]⟩⟩
  obtain ⟨hlo,hli,hlu,hri,hrr,hro,hao,hai,hau,hlx,hrx⟩ := capOuterRectangle_edges hL hR hbottom
  have hOT : capOuterLeft L ≤ capOuterRight R := by linarith
  have hOS : capOuterBottom bottom ≤ b := by linarith
  have hu := verticalJet_contDiffOn modelOpenSquare_isOpen hzO (m+3)
  have hf := actualHighRemainder_contDiffOn hgO modelOpenSquare_isOpen hzO
    (fun p hp => hD p (modelOpenSquare_subset hp)) hyyO m
  have hfI : ContinuousOn (actualHighRemainder (g0+eta) z m)
      (capChart Y '' closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b) :=
    hf.continuousOn.mono (by rintro _ ⟨p,hp,rfl⟩; exact hmapO (hT hp))
  have hcap := hestimate L R bottom top b hL hR hbottom hLR hbt htop hb
  rw [heightUniformCapEstimateRHS_eq_factors] at hcap
  have hp := cap_gradient_estimate_to_physical_images hYs hvar hode hsource heq hu
    modelOpenSquare_isOpen hmapO hLR hbt hOT hOS hS hT hsmall1 hJ hfI hcap
  refine ⟨heightPhysicalCapConstant_pos G Z d c e0 kappa (m+3) L R bottom top b,?_⟩
  change (∫ p in capChart Y '' closedRectangle L R bottom top,
      coordinateGradientSquare (verticalJet z (m+3)) p) ≤ _
  exact hp

end SmoothLocal.Flow

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Flow.exists_C8_one_flow_physical_cap_estimates := @OAI.SmoothLocal.Flow.exists_C8_one_flow_physical_cap_estimates
