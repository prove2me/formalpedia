-- Prove2me | solution 1 for OAI.SmoothLocal.Flow.exists_height_flow_uniform_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:49:12.459693+00:00
-- url     : https://prove2.me/submissions/0aa0e4a9-015b-4cc6-acca-7cc6814f056e

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport
import Theorems.Thm_OAI_SmoothLocal_Flow_capFlowHeight_coordinate_bound

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

namespace SmoothLocal.DriftAlgebra

theorem explicit_drift_remainder
    (h E hy q cxy cyy dyy J ex ey Ey : ℝ)
    (hne : h ≠ 0)
    (energy_y : Ey = 2 * (cxy + dyy) * E - 2 * h * J)
    (energy_jet : q * ex + ey = -2 * J) :
    (Ey / h ^ 2 - E * hy / h ^ 3 - E * (cxy - q * cyy) / h ^ 2 + J / h) -
        q * (ex / h + E * cyy / h ^ 2) - (ey / h + E * dyy / h ^ 2) =
      E / h ^ 2 * (cxy + dyy - hy / h) + J / h := by
  have hey : ey = -2 * J - q * ex := by linarith [energy_jet]
  rw [energy_y, hey]
  field_simp [hne]
  ring

theorem transverse_coefficient_polynomial
    (ell K Ky G Gy rho sigma R : ℝ) :
    K * G * sigma + rho * (Ky * G + K * R + ell * (Ky * G + K * Gy)) =
      (ell + 1) * (G * rho * Ky + K * (rho * Gy + 2 * G * sigma)) +
        K * (rho * R - rho * Gy - (2 * ell + 1) * G * sigma) := by
  ring

theorem transverse_coefficient_factor
    (ell K G Gy rho sigma R : ℝ) (hG : G ≠ 0) (hrho : rho ≠ 0) :
    K * (rho * R - rho * Gy - (2 * ell + 1) * G * sigma) =
      (K * G * rho ^ 2) *
        ((R - Gy) / (G * rho) - (2 * ell + 1) * sigma / rho ^ 2) := by
  field_simp [hG, hrho]

end SmoothLocal.DriftAlgebra

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

theorem coordinateDrift_quotient (q : Coord → ℝ)
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p)
    (hne : h p ≠ 0) :
    coordinateDrift q (fun x => f x / h x) p =
      (coordinateDrift q f p * h p - f p * coordinateDrift q h p) / (h p) ^ 2 := by
  unfold coordinateDrift
  rw [coordPartial_div hf hh hne 0, coordPartial_div hf hh hne 1]
  field_simp [hne]
  ring

theorem coordinateDrift_self_quotient
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p)
    (hne : h p ≠ 0) :
    coordinateDrift (fun x => f x / h x) (fun x => f x / h x) p =
      (coordPartial 0 f p - (f p / h p) * coordPartial 1 f p) / h p -
        (f p / h p) *
          (coordPartial 0 h p - (f p / h p) * coordPartial 1 h p) / h p := by
  rw [coordinateDrift_quotient (fun x => f x / h x) hf hh hne]
  unfold coordinateDrift
  field_simp [hne]

theorem quotient_contDiffOn
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U)
    (hne : ∀ p ∈ U, h p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => f p / h p) U := by
  exact hf.div hh hne

theorem explicitDriftError_contDiffOn
    {E T J : Coord → ℝ} (hU : IsOpen U)
    (hh : ContDiffOn ℝ ∞ h U) (hE : ContDiffOn ℝ ∞ E U)
    (hT : ContDiffOn ℝ ∞ T U) (hJ : ContDiffOn ℝ ∞ J U)
    (hne : ∀ p ∈ U, h p ≠ 0) :
    ContDiffOn ℝ ∞ (explicitDriftError h E T J) U := by
  have hG : ContDiffOn ℝ ∞ (fun p => E p / (h p) ^ 2) U :=
    hE.div (hh.pow 2) (fun p hp => pow_ne_zero 2 (hne p hp))
  have hhy : ContDiffOn ℝ ∞ (coordPartial 1 h) U :=
    partial_contDiffOn hh hU 1
  exact (hG.mul (hT.sub (hhy.div hh hne))).add (hJ.div hh hne)

theorem height_energy_quotient_pos (E h : ℝ) (hE : 0 < E) (hh : h ≠ 0) :
    0 < E / h ^ 2 :=
  div_pos hE (sq_pos_of_ne_zero hh)

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

namespace SmoothLocal.DriftAlgebra

theorem quotient_transport_algebra
    (A B h Ay Bx By hx hy K Ky E Ey a b c d e f J0 J1 : ℝ)
    (hne : h ≠ 0)
    (hdet : A * h - B ^ 2 = K * E)
    (hdety : Ay * h + A * hy - 2 * B * By = Ky * E + K * Ey)
    (hBx : Bx - Ay = -b * A + (a - e) * B + d * h + K * J0)
    (hhx : hx - By = -c * A + (b - f) * B + e * h + K * J1) :
    (Bx - (B / h) * By) / h - (B / h) * (hx - (B / h) * hy) / h -
      (B / h) * (a - 2 * (B / h) * b + (B / h) ^ 2 * c) -
      (d - 2 * (B / h) * e + (B / h) ^ 2 * f) =
        Ky * (E / h ^ 2) + K *
          (Ey / h ^ 2 - E * hy / h ^ 3 -
            (E / h ^ 2) * (b - (B / h) * c) + (J0 - (B / h) * J1) / h) := by
  have hA : A = (B ^ 2 + K * E) / h :=
    (eq_div_iff hne).2 (by linarith [hdet])
  have hAy : Ay = (Ky * E + K * Ey - A * hy + 2 * B * By) / h :=
    (eq_div_iff hne).2 (by linarith [hdety])
  have hBx' : Bx = Ay - b * A + (a - e) * B + d * h + K * J0 := by
    linarith [hBx]
  have hhx' : hx = By - c * A + (b - f) * B + e * h + K * J1 := by
    linarith [hhx]
  rw [hBx', hhx', hAy, hA]
  field_simp [hne]
  ring

end SmoothLocal.DriftAlgebra

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
open scoped ContDiff

namespace SmoothLocal.Geometry

theorem explicitDriftError_scalar_bound
    (h E hy T J c BE Bh BT BJ : ℝ)
    (hc : 0 < c) (hh : c ≤ |h|)
    (hE : |E| ≤ BE) (hhy : |hy| ≤ Bh)
    (hT : |T| ≤ BT) (hJ : |J| ≤ BJ) :
    |E / h ^ 2 * (T - hy / h) + J / h| ≤
      BE / c ^ 2 * (BT + Bh / c) + BJ / c := by
  have hBE : 0 ≤ BE := (abs_nonneg E).trans hE
  have hBh : 0 ≤ Bh := (abs_nonneg hy).trans hhy
  have hBJ : 0 ≤ BJ := (abs_nonneg J).trans hJ
  have hEh : |E / h ^ 2| ≤ BE / c ^ 2 := by
    rw [abs_div, abs_pow]
    exact div_le_div₀ hBE hE (sq_pos_of_pos hc) (pow_le_pow_left₀ hc.le hh 2)
  have hhyh : |hy / h| ≤ Bh / c := by
    rw [abs_div]
    exact div_le_div₀ hBh hhy hc hh
  have hJh : |J / h| ≤ BJ / c := by
    rw [abs_div]
    exact div_le_div₀ hBJ hJ hc hh
  have htri : |T - hy / h| ≤ |T| + |hy / h| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le T (-(hy / h))
  have hsub : |T - hy / h| ≤ BT + Bh / c :=
    htri.trans (add_le_add hT hhyh)
  calc
    |E / h ^ 2 * (T - hy / h) + J / h|
        ≤ |E / h ^ 2 * (T - hy / h)| + |J / h| := abs_add_le _ _
    _ = |E / h ^ 2| * |T - hy / h| + |J / h| := by rw [abs_mul]
    _ ≤ BE / c ^ 2 * (BT + Bh / c) + BJ / c :=
      add_le_add
        (mul_le_mul hEh hsub (abs_nonneg _) (div_nonneg hBE (sq_nonneg c))) hJh

theorem explicitDriftError_pointwise_bound
    (h E T J : Coord → ℝ) (p : Coord) (c BE Bh BT BJ : ℝ)
    (hc : 0 < c) (hh : c ≤ |h p|)
    (hE : |E p| ≤ BE) (hhy : |coordPartial 1 h p| ≤ Bh)
    (hT : |T p| ≤ BT) (hJ : |J p| ≤ BJ) :
    |explicitDriftError h E T J p| ≤
      BE / c ^ 2 * (BT + Bh / c) + BJ / c := by
  exact explicitDriftError_scalar_bound (h p) (E p) (coordPartial 1 h p)
    (T p) (J p) c BE Bh BT BJ hc hh hE hhy hT hJ

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

theorem coordPartial_covHessian (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (i j k : Fin 2) :
    coordPartial i (fun q => covHessian g z q j k) p =
      coordPartial i (coordPartial j (coordPartial k z)) p -
        ∑ a, (coordPartial i (christoffel g a j k) p * coordPartial a z p +
          christoffel g a j k p * coordPartial i (coordPartial a z) p) := by
  have hz1 (a : Fin 2) : DifferentiableAt ℝ (coordPartial a z) p :=
    (((partial_contDiffOn hz hU a) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hg1 (a : Fin 2) : DifferentiableAt ℝ (christoffel g a j k) p :=
    (((christoffel_contDiffOn hg hU a j k) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hz2 : DifferentiableAt ℝ (coordPartial j (coordPartial k z)) p :=
    (((partial_contDiffOn (partial_contDiffOn hz hU k) hU j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hprod (a : Fin 2) : DifferentiableAt ℝ
      (fun q => christoffel g a j k q * coordPartial a z q) p :=
    (hg1 a).mul (hz1 a)
  have hsum : DifferentiableAt ℝ
      (fun q => ∑ a, christoffel g a j k q * coordPartial a z q) p := by
    exact DifferentiableAt.fun_sum fun a _ => hprod a
  change coordPartial i (fun q => coordPartial j (coordPartial k z) q -
      ∑ a, christoffel g a j k q * coordPartial a z q) p = _
  rw [HessianCalculus.coordPartial_sub_at hz2 hsum i,
    HessianCalculus.coordPartial_sum_two
      (fun a q => christoffel g a j k q * coordPartial a z q) hprod i]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  exact HessianCalculus.coordPartial_mul_at (hg1 a) (hz1 a) i

def covDerivHessian (g : MetricField) (z : Coord → ℝ)
    (i j k : Fin 2) (p : Coord) : ℝ :=
  coordPartial i (fun q => covHessian g z q j k) p -
    (∑ a, christoffel g a i j p * covHessian g z p a k) -
    (∑ a, christoffel g a i k p * covHessian g z p j a)

theorem covHessian_commutator (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (i j k : Fin 2) :
    covDerivHessian g z i j k p - covDerivHessian g z j i k p =
      -(∑ a, riemann g a k i j p * coordPartial a z p) := by
  have hGamma (a : Fin 2) : christoffel g a i j p = christoffel g a j i p :=
    christoffel_lower_symm hg hU hp a i j
  unfold covDerivHessian
  rw [coordPartial_covHessian hg hU hz hp i j k,
    coordPartial_covHessian hg hU hz hp j i k,
    coordPartial_comm (partial_contDiffOn hz hU k) hU hp i j]
  simp only [covHessian, riemann, Fin.sum_univ_two]
  rw [hGamma 0, hGamma 1]
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

theorem metricDet_coordPartial (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k : Fin 2) :
    coordPartial k (fun q => (g q).det) p =
      coordPartial k (fun q => g q 0 0) p * g p 1 1 +
        g p 0 0 * coordPartial k (fun q => g q 1 1) p -
        (coordPartial k (fun q => g q 0 1) p * g p 1 0 +
          g p 0 1 * coordPartial k (fun q => g q 1 0) p) := by
  have hd (i j : Fin 2) : DifferentiableAt ℝ (fun q => g q i j) p :=
    (((hg.1 i j) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simp only [Matrix.det_fin_two]
  have hprod₀ : DifferentiableAt ℝ (fun q => g q 0 0 * g q 1 1) p :=
    (hd 0 0).mul (hd 1 1)
  have hprod₁ : DifferentiableAt ℝ (fun q => g q 0 1 * g q 1 0) p :=
    (hd 0 1).mul (hd 1 0)
  rw [HessianCalculus.coordPartial_sub_at hprod₀ hprod₁ k,
    HessianCalculus.coordPartial_mul_at (hd 0 0) (hd 1 1) k,
    HessianCalculus.coordPartial_mul_at (hd 0 1) (hd 1 0) k]

theorem metricDet_partial_trace (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k : Fin 2) :
    coordPartial k (fun q => (g q).det) p =
      2 * (christoffel g 0 k 0 p + christoffel g 1 k 1 p) * (g p).det := by
  rw [metricDet_coordPartial hg hU hp k]
  simp only [metric_compatibility hg hU hp, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem heightEnergy_polynomial_symm (z : Coord → ℝ)
    (hg : SmoothPositiveOn g U) (hp : p ∈ U) :
    heightEnergy g z p = (g p).det -
      (g p 1 1 * (coordPartial 0 z p) ^ 2 -
        2 * g p 0 1 * coordPartial 0 z p * coordPartial 1 z p +
        g p 0 0 * (coordPartial 1 z p) ^ 2) := by
  rw [heightEnergy_polynomial z hg hp, metric_coeff_symm hg hp 1 0]
  ring

namespace CompatibilityCalculus

theorem coordPartial_quadratic
    {A B C X Y : Coord → ℝ} {p : Coord}
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p)
    (hC : DifferentiableAt ℝ C p) (hX : DifferentiableAt ℝ X p)
    (hY : DifferentiableAt ℝ Y p) (k : Fin 2) :
    coordPartial k (fun q => A q * (X q) ^ 2 -
      2 * B q * X q * Y q + C q * (Y q) ^ 2) p =
      coordPartial k A p * (X p) ^ 2 + 2 * A p * X p * coordPartial k X p -
        (2 * coordPartial k B p * X p * Y p +
          2 * B p * coordPartial k X p * Y p +
          2 * B p * X p * coordPartial k Y p) +
        coordPartial k C p * (Y p) ^ 2 + 2 * C p * Y p * coordPartial k Y p := by
  have hd := ((hA.hasFDerivAt.fun_mul (hX.hasFDerivAt.fun_mul hX.hasFDerivAt)).sub
    (((hB.hasFDerivAt.const_mul (2 : ℝ)).fun_mul hX.hasFDerivAt).fun_mul hY.hasFDerivAt)).add
      (hC.hasFDerivAt.fun_mul (hY.hasFDerivAt.fun_mul hY.hasFDerivAt))
  simp only [Pi.add_def, Pi.sub_def] at hd
  simp only [pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

end CompatibilityCalculus

theorem coordPartial_heightEnergy_polynomial
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (k : Fin 2) :
    coordPartial k (heightEnergy g z) p =
      coordPartial k (fun q => (g q).det) p -
        (coordPartial k (fun q => g q 1 1) p * (coordPartial 0 z p) ^ 2 +
          2 * g p 1 1 * coordPartial 0 z p * coordPartial k (coordPartial 0 z) p -
          (2 * coordPartial k (fun q => g q 0 1) p * coordPartial 0 z p * coordPartial 1 z p +
            2 * g p 0 1 * coordPartial k (coordPartial 0 z) p * coordPartial 1 z p +
            2 * g p 0 1 * coordPartial 0 z p * coordPartial k (coordPartial 1 z) p) +
          coordPartial k (fun q => g q 0 0) p * (coordPartial 1 z p) ^ 2 +
          2 * g p 0 0 * coordPartial 1 z p * coordPartial k (coordPartial 1 z) p) := by
  have heq : heightEnergy g z =ᶠ[𝓝 p] (fun q => (g q).det -
      (g q 1 1 * (coordPartial 0 z q) ^ 2 -
        2 * g q 0 1 * coordPartial 0 z q * coordPartial 1 z q +
        g q 0 0 * (coordPartial 1 z q) ^ 2)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact heightEnergy_polynomial_symm z hg hq
  have hdg (i j : Fin 2) : DifferentiableAt ℝ (fun q => g q i j) p :=
    (((hg.1 i j) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdz (i : Fin 2) : DifferentiableAt ℝ (coordPartial i z) p :=
    (((partial_contDiffOn hz hU i) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdet : DifferentiableAt ℝ (fun q => (g q).det) p :=
    (((metricDet_contDiffOn hg) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hquad : DifferentiableAt ℝ (fun q =>
      g q 1 1 * (coordPartial 0 z q) ^ 2 -
        2 * g q 0 1 * coordPartial 0 z q * coordPartial 1 z q +
        g q 0 0 * (coordPartial 1 z q) ^ 2) p :=
    (((hdg 1 1).mul ((hdz 0).pow 2)).sub
      ((((hdg 0 1).const_mul (2 : ℝ)).mul (hdz 0)).mul (hdz 1))).add
        ((hdg 0 0).mul ((hdz 1).pow 2))
  change fderiv ℝ (heightEnergy g z) p (Pi.single k 1) = _
  rw [heq.fderiv_eq]
  change coordPartial k (fun q => (g q).det -
      (g q 1 1 * (coordPartial 0 z q) ^ 2 -
        2 * g q 0 1 * coordPartial 0 z q * coordPartial 1 z q +
        g q 0 0 * (coordPartial 1 z q) ^ 2)) p = _
  rw [HessianCalculus.coordPartial_sub_at hdet hquad k,
    CompatibilityCalculus.coordPartial_quadratic
      (hdg 1 1) (hdg 0 1) (hdg 0 0) (hdz 0) (hdz 1) k]

theorem coordPartial_heightEnergy
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (k : Fin 2) :
    coordPartial k (heightEnergy g z) p =
      2 * (christoffel g 0 k 0 p + christoffel g 1 k 1 p) * heightEnergy g z p -
        2 * (covHessian g z p k 0 *
            (g p 1 1 * coordPartial 0 z p - g p 0 1 * coordPartial 1 z p) +
          covHessian g z p k 1 *
            (g p 0 0 * coordPartial 1 z p - g p 0 1 * coordPartial 0 z p)) := by
  rw [coordPartial_heightEnergy_polynomial hg hU hz hp k,
    metricDet_partial_trace hg hU hp k, heightEnergy_polynomial_symm z hg hp]
  simp only [metric_compatibility hg hU hp, covHessian, Fin.sum_univ_two,
    Matrix.det_fin_two]
  rw [metric_coeff_symm hg hp 1 0]
  ring

theorem heightEnergy_y_quotient
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    coordPartial 1 (heightEnergy g z) p =
      2 * (christoffel g 0 0 1 p + christoffel g 1 1 1 p) * heightEnergy g z p -
        2 * covHessian g z p 1 1 *
          ((g p 0 0 - (covHessian g z p 0 1 / covHessian g z p 1 1) * g p 0 1) *
              coordPartial 1 z p -
            (g p 0 1 - (covHessian g z p 0 1 / covHessian g z p 1 1) * g p 1 1) *
              coordPartial 0 z p) := by
  rw [coordPartial_heightEnergy hg hU hz hp 1,
    christoffel_lower_symm hg hU hp 0 1 0,
    covHessian_symm hg hU hz hp 1 0]
  field_simp [hyy]
  ring

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

def curvatureFactor (g : MetricField) (l k i j : Fin 2) (p : Coord) : ℝ :=
  (if l = i then g p j k else 0) - (if l = j then g p i k else 0)

theorem riemann_factorization (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (l k i j : Fin 2) :
    riemann g l k i j p = gaussianCurvature g p * curvatureFactor g l k i j p := by
  have hvec :
      g p *ᵥ (fun r => riemann g r k i j p) =
      g p *ᵥ (fun r => gaussianCurvature g p * curvatureFactor g r k i j p) := by
    ext a
    change loweredRiemann g a k i j p =
      ∑ r, g p a r * (gaussianCurvature g p * curvatureFactor g r k i j p)
    rw [loweredRiemann_factorization hg hU hp]
    fin_cases i <;> fin_cases j <;> simp [curvatureFactor, Fin.sum_univ_two] <;> ring
  have h := Matrix.mulVec_injective_of_isUnit (hg.2 p hp).isUnit hvec
  exact congrFun h l

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

theorem curvatureDriftError_eq (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    curvatureDriftError g z p =
      darbouxG g z p *
        (connectionTraceY g p -
          coordPartial 1 (fun q => covHessian g z q 1 1) p / covHessian g z p 1 1) +
        driftJ g z p / covHessian g z p 1 1 := rfl

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

theorem connectionTraceY_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (connectionTraceY g) U :=
  (christoffel_contDiffOn hg hU 0 0 1).add (christoffel_contDiffOn hg hU 1 1 1)

theorem driftJ_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (driftJ g z) U := by
  have hq := hessianQuotient_contDiffOn hg hU hz hyy
  exact (((hg.1 0 0).sub (hq.mul (hg.1 0 1))).mul (partial_contDiffOn hz hU 1)).sub
    (((hg.1 0 1).sub (hq.mul (hg.1 1 1))).mul (partial_contDiffOn hz hU 0))

theorem curvatureDriftError_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (curvatureDriftError g z) U :=
  explicitDriftError_contDiffOn hU (covHessian_contDiffOn hg hU hz 1 1)
    (heightEnergy_contDiffOn hg hU hz) (connectionTraceY_contDiffOn hg hU)
    (driftJ_contDiffOn hg hU hz hyy) hyy

theorem darbouxG_pos (g : MetricField) (z : Coord → ℝ) (p : Coord)
    (hE : 0 < heightEnergy g z p) (hyy : covHessian g z p 1 1 ≠ 0) :
    0 < darbouxG g z p :=
  height_energy_quotient_pos (heightEnergy g z p) (covHessian g z p 1 1) hE hyy

theorem curvatureDriftError_bound
    (g : MetricField) (z : Coord → ℝ) (p : Coord) (c BE Bh BT BJ : ℝ)
    (hc : 0 < c) (hh : c ≤ |covHessian g z p 1 1|)
    (hE : |heightEnergy g z p| ≤ BE)
    (hhy : |coordPartial 1 (fun q => covHessian g z q 1 1) p| ≤ Bh)
    (hT : |connectionTraceY g p| ≤ BT) (hJ : |driftJ g z p| ≤ BJ) :
    |curvatureDriftError g z p| ≤ BE / c ^ 2 * (BT + Bh / c) + BJ / c :=
  explicitDriftError_pointwise_bound (fun q => covHessian g z q 1 1)
    (heightEnergy g z) (connectionTraceY g) (driftJ g z) p c BE Bh BT BJ
      hc hh hE hhy hT hJ

theorem driftJ_bound
    (g : MetricField) (z : Coord → ℝ) (p : Coord) (M : ℝ)
    (hMetric : ∀ i j : Fin 2, |g p i j| ≤ M)
    (hHeight : ∀ i : Fin 2, |coordPartial i z p| ≤ M)
    (hq : |hessianQuotient g z p| ≤ (1 / 100 : ℝ)) :
    |driftJ g z p| ≤ (202 / 100 : ℝ) * M ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg (g p 0 0)).trans (hMetric 0 0)
  have heps : (0 : ℝ) ≤ 1 / 100 := by norm_num
  have htriangle (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le a 0 b
  have hqg (i j : Fin 2) :
      |hessianQuotient g z p * g p i j| ≤ (1 / 100 : ℝ) * M := by
    rw [abs_mul]
    exact mul_le_mul hq (hMetric i j) (abs_nonneg _) heps
  have hfactor (a b c d : Fin 2) :
      |g p a b - hessianQuotient g z p * g p c d| ≤ M + (1 / 100 : ℝ) * M :=
    (htriangle _ _).trans (add_le_add (hMetric a b) (hqg c d))
  have hfactor_nonneg : 0 ≤ M + (1 / 100 : ℝ) * M :=
    add_nonneg hM (mul_nonneg heps hM)
  calc
    |driftJ g z p| ≤
        |(g p 0 0 - hessianQuotient g z p * g p 0 1) * coordPartial 1 z p| +
          |(g p 0 1 - hessianQuotient g z p * g p 1 1) * coordPartial 0 z p| :=
      htriangle _ _
    _ = |g p 0 0 - hessianQuotient g z p * g p 0 1| * |coordPartial 1 z p| +
          |g p 0 1 - hessianQuotient g z p * g p 1 1| * |coordPartial 0 z p| := by
      rw [abs_mul, abs_mul]
    _ ≤ (M + (1 / 100 : ℝ) * M) * M + (M + (1 / 100 : ℝ) * M) * M :=
      add_le_add
        (mul_le_mul (hfactor 0 0 0 1) (hHeight 1) (abs_nonneg _) hfactor_nonneg)
        (mul_le_mul (hfactor 0 1 1 1) (hHeight 0) (abs_nonneg _) hfactor_nonneg)
    _ = (202 / 100 : ℝ) * M ^ 2 := by ring

theorem curvatureDriftError_bound_from_low_data
    (g : MetricField) (z : Coord → ℝ) (p : Coord) (c BE Bh BT M : ℝ)
    (hc : 0 < c) (hh : c ≤ |covHessian g z p 1 1|)
    (hE : |heightEnergy g z p| ≤ BE)
    (hhy : |coordPartial 1 (fun q => covHessian g z q 1 1) p| ≤ Bh)
    (hT : |connectionTraceY g p| ≤ BT)
    (hMetric : ∀ i j : Fin 2, |g p i j| ≤ M)
    (hHeight : ∀ i : Fin 2, |coordPartial i z p| ≤ M)
    (hq : |hessianQuotient g z p| ≤ (1 / 100 : ℝ)) :
    |curvatureDriftError g z p| ≤
      BE / c ^ 2 * (BT + Bh / c) + ((202 / 100 : ℝ) * M ^ 2) / c :=
  curvatureDriftError_bound g z p c BE Bh BT ((202 / 100 : ℝ) * M ^ 2)
    hc hh hE hhy hT (driftJ_bound g z p M hMetric hHeight hq)

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
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem covHessian_coordPartial_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (d i j : Fin 2) :
    coordPartial d (fun q => covHessian g z q i j) p =
      coordPartial d (fun q => covHessian g z q j i) p := by
  have heq : (fun q => covHessian g z q i j) =ᶠ[𝓝 p]
      (fun q => covHessian g z q j i) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact covHessian_symm hg hU hz hq i j
  unfold coordPartial
  rw [heq.fderiv_eq]

theorem hessian_transport_Ay_Bx
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) :
    coordPartial 1 (fun q => covHessian g z q 0 0) p -
        coordPartial 0 (fun q => covHessian g z q 0 1) p =
      christoffel g 0 0 1 p * covHessian g z p 0 0 +
        (christoffel g 1 0 1 p - christoffel g 0 0 0 p) * covHessian g z p 0 1 -
        christoffel g 1 0 0 p * covHessian g z p 1 1 +
        gaussianCurvature g p * (g p 0 1 * coordPartial 0 z p -
          g p 0 0 * coordPartial 1 z p) := by
  have hc := covHessian_commutator hg hU hz hp 0 1 0
  simp only [covDerivHessian, Fin.sum_univ_two, riemann_factorization hg hU hp] at hc
  simp [curvatureFactor] at hc
  simp only [covHessian_coordPartial_symm hg hU hz hp 0 1 0,
    covHessian_symm hg hU hz hp 1 0,
    christoffel_lower_symm hg hU hp 0 1 0,
    christoffel_lower_symm hg hU hp 1 1 0,
    metric_coeff_symm hg hp 1 0] at hc
  linear_combination -hc

theorem hessian_transport_hx_By
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) :
    coordPartial 0 (fun q => covHessian g z q 1 1) p -
        coordPartial 1 (fun q => covHessian g z q 0 1) p =
      -christoffel g 0 1 1 p * covHessian g z p 0 0 +
        (christoffel g 0 0 1 p - christoffel g 1 1 1 p) * covHessian g z p 0 1 +
        christoffel g 1 0 1 p * covHessian g z p 1 1 +
        gaussianCurvature g p * (g p 0 1 * coordPartial 1 z p -
          g p 1 1 * coordPartial 0 z p) := by
  have hc := covHessian_commutator hg hU hz hp 0 1 1
  simp only [covDerivHessian, Fin.sum_univ_two, riemann_factorization hg hU hp] at hc
  simp [curvatureFactor] at hc
  simp only [covHessian_symm hg hU hz hp 1 0,
    christoffel_lower_symm hg hU hp 0 1 0,
    christoffel_lower_symm hg hU hp 1 1 0] at hc
  linear_combination hc

theorem darboux_determinant_derivative
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U)
    (hDarboux : ∀ q ∈ U, (covHessian g z q).det =
      gaussianCurvature g q * heightEnergy g z q)
    (hp : p ∈ U) (d : Fin 2) :
    coordPartial d (fun q => covHessian g z q 0 0) p * covHessian g z p 1 1 +
        covHessian g z p 0 0 * coordPartial d (fun q => covHessian g z q 1 1) p -
        2 * covHessian g z p 0 1 * coordPartial d (fun q => covHessian g z q 0 1) p =
      coordPartial d (gaussianCurvature g) p * heightEnergy g z p +
        gaussianCurvature g p * coordPartial d (heightEnergy g z) p := by
  have heq : (fun q => covHessian g z q 0 0 * covHessian g z q 1 1 -
      covHessian g z q 0 1 * covHessian g z q 0 1) =ᶠ[𝓝 p]
      (fun q => gaussianCurvature g q * heightEnergy g z q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hq 1 0] using hDarboux q hq
  have hdH (i j : Fin 2) : DifferentiableAt ℝ (fun q => covHessian g z q i j) p :=
    (((covHessian_contDiffOn hg hU hz i j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdK : DifferentiableAt ℝ (gaussianCurvature g) p :=
    (((gaussianCurvature_contDiffOn hg hU) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdE : DifferentiableAt ℝ (heightEnergy g z) p :=
    (((heightEnergy_contDiffOn hg hU hz) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hd : coordPartial d
      (fun q => covHessian g z q 0 0 * covHessian g z q 1 1 -
        covHessian g z q 0 1 * covHessian g z q 0 1) p =
      coordPartial d (fun q => gaussianCurvature g q * heightEnergy g z q) p := by
    unfold coordPartial
    rw [heq.fderiv_eq]
  have hdprod : DifferentiableAt ℝ
      (fun q => covHessian g z q 0 0 * covHessian g z q 1 1) p :=
    (hdH 0 0).mul (hdH 1 1)
  have hdsq : DifferentiableAt ℝ
      (fun q => covHessian g z q 0 1 * covHessian g z q 0 1) p :=
    (hdH 0 1).mul (hdH 0 1)
  rw [HessianCalculus.coordPartial_sub_at hdprod hdsq d,
    HessianCalculus.coordPartial_mul_at (hdH 0 0) (hdH 1 1) d,
    HessianCalculus.coordPartial_mul_at (hdH 0 1) (hdH 0 1) d,
    HessianCalculus.coordPartial_mul_at hdK hdE d] at hd
  linear_combination hd

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

theorem boxPoint_hasDerivAt_s (t s : ℝ) :
    HasDerivAt (boxPoint t) (Pi.single 1 (1 : ℝ) : Coord) s := by
  change HasDerivAt (fun x : ℝ => t • (Pi.single 0 (1 : ℝ) : Coord) +
    x • (Pi.single 1 (1 : ℝ) : Coord)) (Pi.single 1 (1 : ℝ) : Coord) s
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id s).smul_const (Pi.single 1 (1 : ℝ) : Coord)).const_add
      (t • (Pi.single 0 (1 : ℝ) : Coord))

variable {tl tr sb st : ℝ} {f g : Coord → ℝ}

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
open scoped ContDiff Matrix BigOperators

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem hessian_quotient_transport
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ q ∈ U, (covHessian g z q).det = gaussianCurvature g q * heightEnergy g z q)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0) :
    coordinateDrift (hessianQuotient g z) (hessianQuotient g z) p -
      hessianQuotient g z p * christoffelAlongD g p (hessianQuotient g z p) 0 -
      christoffelAlongD g p (hessianQuotient g z p) 1 =
        coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
        gaussianCurvature g p *
          (coordPartial 1 (heightEnergy g z) p / (covHessian g z p 1 1) ^ 2 -
            heightEnergy g z p * coordPartial 1 (fun q => covHessian g z q 1 1) p /
              (covHessian g z p 1 1) ^ 3 -
            darbouxG g z p * (christoffel g 0 0 1 p -
              hessianQuotient g z p * christoffel g 0 1 1 p) +
            driftJ g z p / covHessian g z p 1 1) := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD p hp
  have hBx : coordPartial 0 (fun q => covHessian g z q 0 1) p -
      coordPartial 1 (fun q => covHessian g z q 0 0) p =
      -christoffel g 0 0 1 p * covHessian g z p 0 0 +
      (christoffel g 0 0 0 p - christoffel g 1 0 1 p) * covHessian g z p 0 1 +
      christoffel g 1 0 0 p * covHessian g z p 1 1 +
      gaussianCurvature g p * (g p 0 0 * coordPartial 1 z p - g p 0 1 * coordPartial 0 z p) := by
    linear_combination -hessian_transport_Ay_Bx hg hU hz hp
  have hs := SmoothLocal.DriftAlgebra.quotient_transport_algebra
    (covHessian g z p 0 0) (covHessian g z p 0 1) (covHessian g z p 1 1)
    (coordPartial 1 (fun q => covHessian g z q 0 0) p)
    (coordPartial 0 (fun q => covHessian g z q 0 1) p)
    (coordPartial 1 (fun q => covHessian g z q 0 1) p)
    (coordPartial 0 (fun q => covHessian g z q 1 1) p)
    (coordPartial 1 (fun q => covHessian g z q 1 1) p)
    (gaussianCurvature g p) (coordPartial 1 (gaussianCurvature g) p)
    (heightEnergy g z p) (coordPartial 1 (heightEnergy g z) p)
    (christoffel g 0 0 0 p) (christoffel g 0 0 1 p) (christoffel g 0 1 1 p)
    (christoffel g 1 0 0 p) (christoffel g 1 0 1 p) (christoffel g 1 1 1 p)
    (g p 0 0 * coordPartial 1 z p - g p 0 1 * coordPartial 0 z p)
    (g p 0 1 * coordPartial 1 z p - g p 1 1 * coordPartial 0 z p)
    hyy hdet (darboux_determinant_derivative hg hU hz hD hp 1) hBx
    (hessian_transport_hx_By hg hU hz hp)
  have hdH (i j : Fin 2) : DifferentiableAt ℝ (fun q => covHessian g z q i j) p :=
    (((covHessian_contDiffOn hg hU hz i j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hqD := coordinateDrift_self_quotient (hdH 0 1) (hdH 1 1) hyy
  change coordinateDrift (hessianQuotient g z) (hessianQuotient g z) p = _ at hqD
  rw [hqD, christoffelAlongD_eq hg hU hp, christoffelAlongD_eq hg hU hp]
  dsimp only [hessianQuotient, darbouxG, driftJ]
  convert hs using 1
  ring

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

theorem heightEnergy_jet_contraction (hg : SmoothPositiveOn g U) (hp : p ∈ U) :
    hessianQuotient g z p * coordPartial 0 (jetEnergy g p) (fun r => coordPartial r z p) +
      coordPartial 1 (jetEnergy g p) (fun r => coordPartial r z p) = -2 * driftJ g z p := by
  rw [coordPartial_jetEnergy, coordPartial_jetEnergy]
  norm_num
  rw [metric_coeff_symm hg hp 1 0]
  unfold driftJ
  ring

theorem geometric_quotient_drift
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ q ∈ U, (covHessian g z q).det = gaussianCurvature g q * heightEnergy g z q)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0) :
    coordinateDrift (hessianQuotient g z) (hessianQuotient g z) p -
      hessianQuotient g z p * heightPFirst g z 0 p - heightPFirst g z 1 p =
        coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
          gaussianCurvature g p * curvatureDriftError g z p := by
  have hd := hessian_quotient_transport hg hU hz hD hp hyy
  have he : coordPartial 1 (heightEnergy g z) p =
      2 * (christoffel g 0 0 1 p + christoffel g 1 1 1 p) * heightEnergy g z p -
        2 * covHessian g z p 1 1 * driftJ g z p :=
    heightEnergy_y_quotient hg hU hz hp hyy
  have hr := SmoothLocal.DriftAlgebra.explicit_drift_remainder
    (covHessian g z p 1 1) (heightEnergy g z p)
    (coordPartial 1 (fun q => covHessian g z q 1 1) p)
    (hessianQuotient g z p)
    (christoffel g 0 0 1 p) (christoffel g 0 1 1 p) (christoffel g 1 1 1 p)
    (driftJ g z p)
    (coordPartial 0 (jetEnergy g p) (fun r => coordPartial r z p))
    (coordPartial 1 (jetEnergy g p) (fun r => coordPartial r z p))
    (coordPartial 1 (heightEnergy g z) p) hyy he (heightEnergy_jet_contraction hg hp)
  rw [heightPFirst_eq hg hU hp hyy 0, heightPFirst_eq hg hU hp hyy 1,
    curvatureDriftError_eq]
  dsimp only [darbouxG, connectionTraceY] at hd ⊢
  linear_combination hd + gaussianCurvature g p * hr

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
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry.CoordinateBound

theorem congr_on {f h : Coord → ℝ} {U : Set Coord} {n : ℕ} {M : ℝ}
    (hU : IsOpen U) (hf : CoordinateBound f U n M) (he : EqOn h f U) :
    CoordinateBound h U n M := by
  intro ds hds p hp
  have hlocal : h =ᶠ[𝓝 p] f := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact he hx
  rw [(iteratedCoordPartial_eventuallyEq hlocal ds).self_of_nhds]
  exact hf ds hds p hp

theorem mul_through_one {f h : Coord → ℝ} {U : Set Coord} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfB : CoordinateBound f U 1 A) (hhB : CoordinateBound h U 1 B) :
    CoordinateBound (fun x => f x * h x) U 1 (2 * A * B) := by
  intro ds hds p hp
  have hab (vs ws : List (Fin 2)) (hv : vs.length ≤ 1) (hw : ws.length ≤ 1) :
      |iteratedCoordPartial vs f p * iteratedCoordPartial ws h p| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul (hfB vs hv p hp) (hhB ws hw p hp) (abs_nonneg _) hA
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  cases ds with
  | nil => exact (hab [] [] (by norm_num) (by norm_num)).trans (by nlinarith)
  | cons i ds =>
    cases ds with
    | nil =>
      rw [LowQuotient.product_one hf hh hU hp i]
      exact ((abs_add_le _ _).trans
        (add_le_add (hab [i] [] (by norm_num) (by norm_num))
          (hab [] [i] (by norm_num) (by norm_num)))).trans (le_of_eq (by ring))
    | cons j ds => simp only [List.length_cons] at hds; omega

theorem div_through_one {f h : Coord → ℝ} {U : Set Coord} {A B c : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c)
    (hfB : CoordinateBound f U 1 A) (hhB : CoordinateBound h U 1 B)
    (hden : ∀ p ∈ U, c ≤ |h p|) :
    CoordinateBound (fun x => f x / h x) U 1 (A / c + (A + B * (A / c)) / c) := by
  have hne := LowQuotient.denominator_ne_zero hc hden
  have hval (p : Coord) (hp : p ∈ U) : |f p / h p| ≤ A / c :=
    LowQuotient.abs_div_bound hA (hfB [] (by norm_num) p hp) hc (hden p hp)
  have h0 : 0 ≤ A / c := by positivity
  have h1 : 0 ≤ (A + B * (A / c)) / c := by positivity
  intro ds hds p hp
  cases ds with
  | nil => exact (hval p hp).trans (by linarith)
  | cons i ds =>
    cases ds with
    | nil =>
      rw [LowQuotient.quotient_one hf hh hU hp hne i]
      have hprod : |coordPartial i h p * (f p / h p)| ≤ B * (A / c) := by
        rw [abs_mul]
        exact mul_le_mul (hhB [i] (by norm_num) p hp) (hval p hp) (abs_nonneg _) hB
      have hnum := (abs_sub (coordPartial i f p) (coordPartial i h p * (f p / h p))).trans
        (add_le_add (hfB [i] (by norm_num) p hp) hprod)
      exact (LowQuotient.abs_div_bound (by positivity) hnum hc (hden p hp)).trans (by linarith)
    | cons j ds => simp only [List.length_cons] at hds; omega

end SmoothLocal.Geometry.CoordinateBound

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
open Set Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord} {G d : ℝ}

theorem riemann_coordinate_bound_one
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) (l k i j : Fin 2) :
    CoordinateBound (riemann g l k i j) U 1 (riemannFirstBound G d) := by
  have hΓ := christoffelJetBound_nonneg hG hd
  have hΓB (a b c : Fin 2) := christoffel_coordinate_bound hg hU hG hd hgB hdet a b c
  have hΓ1 (a b c : Fin 2) : CoordinateBound (christoffel g a b c) U 1 (christoffelJetBound G d) :=
    (hΓB a b c).mono (by norm_num) le_rfl
  have hΓd (a b c e : Fin 2) : CoordinateBound (coordPartial e (christoffel g a b c)) U 1
      (christoffelJetBound G d) :=
    ((hΓB a b c).mono (by norm_num : 2 ≤ 3) le_rfl).partial_bound e
  have hΓs (a b c : Fin 2) := christoffel_contDiffOn hg hU a b c
  have hm (m : Fin 2) := CoordinateBound.sub
    ((hΓs m j k).mul (hΓs l i m)) ((hΓs m i k).mul (hΓs l j m)) hU
    (CoordinateBound.mul_through_one (hΓs m j k) (hΓs l i m) hU hΓ hΓ (hΓ1 m j k) (hΓ1 l i m))
    (CoordinateBound.mul_through_one (hΓs m i k) (hΓs l j m) hU hΓ hΓ (hΓ1 m i k) (hΓ1 l j m))
  have hms (m : Fin 2) := ((hΓs m j k).mul (hΓs l i m)).sub ((hΓs m i k).mul (hΓs l j m))
  have hs := CoordinateBound.add (hms 0) (hms 1) hU (hm 0) (hm 1)
  have hdiff := CoordinateBound.sub (partial_contDiffOn (hΓs l j k) hU i)
    (partial_contDiffOn (hΓs l i k) hU j) hU (hΓd l j k i) (hΓd l i k j)
  have hb := CoordinateBound.add
    ((partial_contDiffOn (hΓs l j k) hU i).sub (partial_contDiffOn (hΓs l i k) hU j))
    ((hms 0).add (hms 1)) hU hdiff hs
  convert hb using 1 <;> first
    | (funext p; simp only [riemann, Fin.sum_univ_two])
    | (dsimp [riemannFirstBound]; ring)

theorem gaussianCurvature_coordinate_bound_one
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) :
    CoordinateBound (gaussianCurvature g) U 1 (curvatureFirstBound G d) := by
  have hR := riemannFirstBound_nonneg hG hd
  have hprod (l : Fin 2) := CoordinateBound.mul_through_one (hg.1 0 l)
    (riemann_contDiffOn hg hU l 1 0 1) hU hG hR
    ((hgB 0 l).mono (by norm_num) le_rfl)
    (riemann_coordinate_bound_one hg hU hG hd hgB hdet l 1 0 1)
  have hprodS (l : Fin 2) := (hg.1 0 l).mul (riemann_contDiffOn hg hU l 1 0 1)
  have hsum := CoordinateBound.add (hprodS 0) (hprodS 1) hU (hprod 0) (hprod 1)
  have hn : CoordinateBound (fun p => g p 0 0 * riemann g 0 1 0 1 p +
      g p 0 1 * riemann g 1 1 0 1 p) U 1 (curvatureNumeratorFirstBound G d) := by
    convert hsum using 1
    dsimp [curvatureNumeratorFirstBound]
    ring
  have hnb : 0 ≤ curvatureNumeratorFirstBound G d := by dsimp [curvatureNumeratorFirstBound]; positivity
  have hdb : CoordinateBound (fun p => (g p).det) U 1 (16 * G^2) :=
    (metricDet_coordinate_bound hg hU hG (fun i j => (hgB i j).mono (by norm_num) le_rfl)).mono
      (by norm_num) le_rfl
  have hb := CoordinateBound.div_through_one ((hprodS 0).add (hprodS 1))
    (metricDet_contDiffOn hg) hU hnb (by positivity : 0 ≤ 16 * G^2) hd hn hdb hdet
  convert hb using 1 <;> try rfl
  funext p
  simp only [gaussianCurvature, Fin.sum_univ_two]

end SmoothLocal.Geometry

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

theorem capFlowHeight_partial_initial_pos {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) : 0 < coordPartial 1 (capFlowHeight Y) p := by
  rw [← (capFlowHeight_hasDerivAt_initial hY hp).deriv]
  exact hvar (p 1) hp.2 (p 0) hp.1

theorem capChartRho_pos {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) : 0 < capChartRho Y p :=
  one_div_pos.mpr (capFlowHeight_partial_initial_pos hY hvar hp)

theorem capChartRho_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s) :
    ContDiffOn ℝ ∞ (capChartRho Y) capChartDomain :=
  contDiffOn_const.div (partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1)
    (fun _ hp => (capFlowHeight_partial_initial_pos hY hvar hp).ne')

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

theorem capChartRho_partial_initial
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) :
    coordPartial 1 (capChartRho Y) p =
      -coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p /
        (coordPartial 1 (capFlowHeight Y) p) ^ 2 := by
  have hYs := partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1
  change coordPartial 1 (fun z => (1 : ℝ) / coordPartial 1 (capFlowHeight Y) z) p = _
  rw [coordPartial_div (differentiableAt_const (1 : ℝ))
    ((hYs.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp))
    (capFlowHeight_partial_initial_pos hY hvar hp).ne' 1]
  simp [coordPartial]

theorem capChartSigma_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s) :
    ContDiffOn ℝ ∞ (capChartSigma Y) capChartDomain := by
  have hYs := partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1
  exact (partial_contDiffOn hYs capChartDomain_isOpen 1).neg.div (hYs.pow 3)
    (fun p hp => pow_ne_zero 3 (capFlowHeight_partial_initial_pos hY hvar hp).ne')

theorem capTransportA_partial_initial {a : Coord → ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    coordPartial 1 (capTransportA Y a) p =
      capChartRho Y p * capPullback Y (coordPartial 1 a) p +
        2 * capPullback Y a p * capChartSigma Y p := by
  have hPa : DifferentiableAt ℝ (capPullback Y a) p :=
    ((capPullback_contDiffOn hY ha hmap).contDiffAt
      (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hrho : DifferentiableAt ℝ (capChartRho Y) p :=
    ((capChartRho_contDiffOn hY hvar).contDiffAt
      (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  unfold capTransportA
  simp only [pow_two]
  have hrhorho : DifferentiableAt ℝ (fun z => capChartRho Y z * capChartRho Y z) p :=
    hrho.mul hrho
  rw [HessianCalculus.coordPartial_mul_at hPa hrhorho 1,
    HessianCalculus.coordPartial_mul_at hrho hrho 1,
    capPullback_partial_initial hY hp
      ((ha.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp)),
    capChartRho_partial_initial hY hvar hp]
  unfold capChartRho capChartSigma
  field_simp [(capFlowHeight_partial_initial_pos hY hvar hp).ne']
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

theorem covHessian_coordinate_bound_closed_square
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|) (i j : Fin 2) :
    CoordinateBound (fun p => covHessian g z p i j) modelSquare 3 (hessianJetBound G Z d) := by
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun a b => (hg.1 a b).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  have hBI := covHessian_coordinate_bound hgI isOpen_interior (hz.mono hIU) hG hZ hd
    (fun a b => (hgB a b).restrict_domain interior_subset) (hzB.restrict_domain interior_subset)
    (fun p hp => hdet p (interior_subset hp)) i j
  exact CoordinateBound.of_modelSquare_interior (covHessian_contDiffOn hg hU hz i j) hU hSU hBI

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

def initialFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun s => Y s p.1) p.2

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

end ActualFlow
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

theorem heightOriginalA_partial_y (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U) :
    coordPartial 1 (heightOriginalA g z) p =
      coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
        gaussianCurvature g p * coordPartial 1 (darbouxG g z) p := by
  exact HessianCalculus.coordPartial_mul_at
    (((gaussianCurvature_contDiffOn hg hU).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
    (((darbouxG_contDiffOn hg hU hz hyy).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) 1

theorem heightOriginalC0_eq (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U) (ell : ℕ) :
    heightOriginalC0 g z ell p =
      coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
        gaussianCurvature g p * curvatureDriftError g z p +
        (ell : ℝ) * (coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
          gaussianCurvature g p * coordPartial 1 (darbouxG g z) p) := by
  unfold heightOriginalC0
  rw [geometric_quotient_drift hg hU hz hD hp (hyy p hp), heightOriginalA_partial_y hg hU hz hyy hp]

theorem heightChartA_partial_initial
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    coordPartial 1 (heightChartA g z Y) p =
      darbouxG g z (capChart Y p) * capChartRho Y p * coordPartial 1 (gaussianCurvature g) (capChart Y p) +
        gaussianCurvature g (capChart Y p) *
          (capChartRho Y p * coordPartial 1 (darbouxG g z) (capChart Y p) +
            2 * darbouxG g z (capChart Y p) * capChartSigma Y p) := by
  rw [heightChartA, capTransportA_partial_initial hY hvar
    (heightOriginalA_contDiffOn hg hU hz hyy) hU hmap hp]
  unfold capPullback
  rw [heightOriginalA_partial_y hg hU hz hyy (hmap hp)]
  unfold heightOriginalA
  ring

theorem heightChartC_expanded
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) (ell : ℕ) :
    heightChartC g z Y ell p =
      gaussianCurvature g (capChart Y p) * darbouxG g z (capChart Y p) * capChartSigma Y p +
        capChartRho Y p *
          (coordPartial 1 (gaussianCurvature g) (capChart Y p) * darbouxG g z (capChart Y p) +
            gaussianCurvature g (capChart Y p) * curvatureDriftError g z (capChart Y p) +
            (ell : ℝ) * (coordPartial 1 (gaussianCurvature g) (capChart Y p) * darbouxG g z (capChart Y p) +
              gaussianCurvature g (capChart Y p) * coordPartial 1 (darbouxG g z) (capChart Y p))) := by
  unfold heightChartC capTransportC capPullback heightOriginalA
  rw [heightOriginalC0_eq hg hU hz hD hyy (hmap hp) ell]
  ring

theorem heightChartC_factor
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hE : ∀ p ∈ U, 0 < heightEnergy g z p)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) (ell : ℕ) :
    heightChartC g z Y ell p = ((ell : ℝ) + 1) * coordPartial 1 (heightChartA g z Y) p +
      heightChartA g z Y p * heightChartRemainder g z Y ell p := by
  have hGne := (darbouxG_pos g z (capChart Y p) (hE _ (hmap hp)) (hyy _ (hmap hp))).ne'
  have hrhone := (capChartRho_pos hY hvar hp).ne'
  rw [heightChartC_expanded hg hU hz hD hyy hmap hp ell,
    heightChartA_partial_initial hg hU hz hyy hY hvar hmap hp]
  unfold heightChartA capTransportA heightOriginalA heightChartRemainder capPullback
  rw [SmoothLocal.DriftAlgebra.transverse_coefficient_polynomial,
    SmoothLocal.DriftAlgebra.transverse_coefficient_factor _ _ _ _ _ _ _ hGne hrhone]

theorem heightChartRemainder_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hE : ∀ p ∈ U, 0 < heightEnergy g z p)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightChartRemainder g z Y ell) capChartDomain := by
  have hG := darbouxG_contDiffOn hg hU hz hyy
  have hPG := capPullback_contDiffOn hY hG hmap
  have hPGy := capPullback_contDiffOn hY (partial_contDiffOn hG hU 1) hmap
  have hPR := capPullback_contDiffOn hY (curvatureDriftError_contDiffOn hg hU hz hyy) hmap
  have hrho := capChartRho_contDiffOn hY hvar
  have hsigma := capChartSigma_contDiffOn hY hvar
  exact ((hPR.sub hPGy).div (hPG.mul hrho) (fun _ hp =>
    mul_ne_zero (darbouxG_pos g z _ (hE _ (hmap hp)) (hyy _ (hmap hp))).ne'
      (capChartRho_pos hY hvar hp).ne')).sub
    ((contDiffOn_const.mul hsigma).div (hrho.pow 2)
      (fun _ hp => pow_ne_zero 2 (capChartRho_pos hY hvar hp).ne'))

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

theorem heightChartB_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hmap : MapsTo (capChart Y) capChartDomain U) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightChartB g z Y ell) capChartDomain :=
  capPullback_contDiffOn hY (heightOriginalB_contDiffOn hg hU hz hyy ell) hmap

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
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

theorem heightEnergy_coordinate_bound
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G)
    (hzB : CoordinateBound z U 4 Z) :
    CoordinateBound (heightEnergy g z) U 3 (heightEnergyJetBound G Z) := by
  have hzi (i : Fin 2) := partial_contDiffOn hz hU i
  have hzBi (i : Fin 2) : CoordinateBound (coordPartial i z) U 3 Z := hzB.partial_bound i
  have hsquare (i : Fin 2) : CoordinateBound (fun p => (coordPartial i z p)^2) U 3 (8 * Z^2) := by
    convert CoordinateBound.mul_through_three (hzi i) (hzi i) hU hZ hZ (hzBi i) (hzBi i) using 1 <;>
      simp only [pow_two, mul_assoc]
  have hdiag0 := CoordinateBound.mul_through_three (hg.1 1 1) ((hzi 0).pow 2) hU hG
    (by positivity : 0 ≤ 8 * Z^2) (hgB 1 1) (hsquare 0)
  have hdiag1 := CoordinateBound.mul_through_three (hg.1 0 0) ((hzi 1).pow 2) hU hG
    (by positivity : 0 ≤ 8 * Z^2) (hgB 0 0) (hsquare 1)
  have hsum := CoordinateBound.add (hg.1 0 1) (hg.1 1 0) hU (hgB 0 1) (hgB 1 0)
  have hcross1 := CoordinateBound.mul_through_three ((hg.1 0 1).add (hg.1 1 0))
    (hzi 0) hU (by positivity : 0 ≤ G + G) hZ hsum (hzBi 0)
  have hcross := CoordinateBound.mul_through_three
    (((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)) (hzi 1) hU
    (by positivity : 0 ≤ 8 * (G + G) * Z) hZ hcross1 (hzBi 1)
  have hinner := CoordinateBound.add
    (((hg.1 1 1).mul ((hzi 0).pow 2)).sub ((((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)).mul (hzi 1)))
    ((hg.1 0 0).mul ((hzi 1).pow 2)) hU
    (CoordinateBound.sub ((hg.1 1 1).mul ((hzi 0).pow 2))
      ((((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)).mul (hzi 1)) hU hdiag0 hcross) hdiag1
  have hfull := CoordinateBound.sub (metricDet_contDiffOn hg)
    ((((hg.1 1 1).mul ((hzi 0).pow 2)).sub
      ((((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)).mul (hzi 1))).add
        ((hg.1 0 0).mul ((hzi 1).pow 2))) hU (metricDet_coordinate_bound hg hU hG hgB) hinner
  have hc : 16 * G^2 + (8 * G * (8 * Z^2) + 8 * (8 * (G + G) * Z) * Z + 8 * G * (8 * Z^2)) =
      heightEnergyJetBound G Z := by dsimp [heightEnergyJetBound]; ring
  rw [hc] at hfull
  exact CoordinateBound.congr_on hU hfull (fun p hp => heightEnergy_polynomial z hg hp)

theorem darbouxG_coordinate_bound
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) :
    CoordinateBound (darbouxG g z) U 3 (darbouxGJetBound G Z d c) := by
  have hH := hessianJetBound_nonneg hG hZ hd
  have hE := heightEnergyJetBound_nonneg (Z := Z) hG
  have hh := covHessian_contDiffOn hg hU hz 1 1
  have hhB := covHessian_coordinate_bound hg hU hz hG hZ hd hgB hzB hdet 1 1
  have hhsq : CoordinateBound (fun p => (covHessian g z p 1 1)^2) U 3
      (8 * (hessianJetBound G Z d)^2) := by
    convert CoordinateBound.mul_through_three hh hh hU hH hH hhB hhB using 1 <;>
      simp only [pow_two, mul_assoc]
  have hEB := heightEnergy_coordinate_bound hg hU hz hG hZ
    (fun i j => (hgB i j).mono (by norm_num) le_rfl) (hzB.mono (by norm_num) le_rfl)
  let N := heightEnergyJetBound G Z + 8 * (hessianJetBound G Z d)^2
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hn : heightEnergyJetBound G Z ≤ N := by dsimp [N]; nlinarith [sq_nonneg (hessianJetBound G Z d)]
  have hb : 8 * (hessianJetBound G Z d)^2 ≤ N := by dsimp [N]; linarith
  have hden (p : Coord) (hp : p ∈ U) : c^2 ≤ |(covHessian g z p 1 1)^2| := by
    rw [abs_pow]
    exact pow_le_pow_left₀ hc.le (hyy p hp) 2
  intro ds hds p hp
  exact LowQuotient.quotient_bound_through_three (heightEnergy_contDiffOn hg hU hz)
    (hh.pow 2) hU hN (pow_pos hc 2) (hEB.mono le_rfl hn) (hhsq.mono le_rfl hb) hden ds hds hp

theorem darbouxG_lower_of_energy_floor
    (g : MetricField) (z : Coord → ℝ) (p : Coord) {e0 H : ℝ}
    (he0 : 0 < e0) (hE : e0 ≤ heightEnergy g z p) (hH : 0 ≤ H)
    (hupper : |covHessian g z p 1 1| ≤ H) (hne : covHessian g z p 1 1 ≠ 0) :
    e0 / (1 + H)^2 ≤ darbouxG g z p := by
  have hsq : (covHessian g z p 1 1)^2 ≤ (1 + H)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (covHessian g z p 1 1))
      (hupper.trans (by linarith : H ≤ 1 + H)) 2
    simpa only [sq_abs] using hh
  have hl : 0 ≤ e0 / (1 + H)^2 := by positivity
  have heq : e0 / (1 + H)^2 * (1 + H)^2 = e0 :=
    div_mul_cancel₀ _ (pow_ne_zero 2 (by linarith : (1 : ℝ) + H ≠ 0))
  unfold darbouxG
  apply (le_div_iff₀ (sq_pos_of_ne_zero hne)).mpr
  calc
    _ ≤ e0 / (1 + H)^2 * (1 + H)^2 := mul_le_mul_of_nonneg_left hsq hl
    _ = e0 := heq
    _ ≤ heightEnergy g z p := hE

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

theorem height_jetEnergy_first_coordinate_bound
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G)
    (hzB : CoordinateBound z U 4 Z) (i : Fin 2) :
    CoordinateBound (fun p => coordPartial i (jetEnergy g p) (fun r => coordPartial r z p)) U 3
      (32 * G * Z) := by
  have hzS (j : Fin 2) := partial_contDiffOn hz hU j
  have hzD (j : Fin 2) : CoordinateBound (coordPartial j z) U 3 Z := hzB.partial_bound j
  have hdiag (a j : Fin 2) := CoordinateBound.const_mul
    ((hg.1 a a).mul (hzS j)) hU
    (CoordinateBound.mul_through_three (hg.1 a a) (hzS j) hU hG hZ (hgB a a) (hzD j)) (2 : ℝ)
  have hoff (j : Fin 2) := CoordinateBound.mul_through_three
    ((hg.1 0 1).add (hg.1 1 0)) (hzS j) hU (by positivity : 0 ≤ G + G) hZ
    (CoordinateBound.add (hg.1 0 1) (hg.1 1 0) hU (hgB 0 1) (hgB 1 0)) (hzD j)
  fin_cases i
  · have hb := CoordinateBound.sub (((hg.1 0 1).add (hg.1 1 0)).mul (hzS 1))
      (contDiffOn_const.mul ((hg.1 1 1).mul (hzS 0))) hU (hoff 1) (hdiag 1 0)
    have hc : 8 * (G + G) * Z + |(2 : ℝ)| * (8 * G * Z) = 32 * G * Z := by norm_num; ring
    rw [hc] at hb
    apply CoordinateBound.congr_on hU hb
    intro p hp
    change coordPartial 0 (jetEnergy g p) (fun r => coordPartial r z p) =
      (g p 0 1 + g p 1 0) * coordPartial 1 z p - 2 * (g p 1 1 * coordPartial 0 z p)
    rw [coordPartial_jetEnergy]
    norm_num
    ring
  · have hb := CoordinateBound.sub (((hg.1 0 1).add (hg.1 1 0)).mul (hzS 0))
      (contDiffOn_const.mul ((hg.1 0 0).mul (hzS 1))) hU (hoff 0) (hdiag 0 1)
    have hc : 8 * (G + G) * Z + |(2 : ℝ)| * (8 * G * Z) = 32 * G * Z := by norm_num; ring
    rw [hc] at hb
    apply CoordinateBound.congr_on hU hb
    intro p hp
    change coordPartial 1 (jetEnergy g p) (fun r => coordPartial r z p) =
      (g p 0 1 + g p 1 0) * coordPartial 0 z p - 2 * (g p 0 0 * coordPartial 1 z p)
    rw [coordPartial_jetEnergy]
    norm_num
    ring

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}

theorem height_christoffelAlongD_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) (i : Fin 2) :
    CoordinateBound (fun p => christoffelAlongD g p (hessianQuotient g z p) i) U 3
      (heightAlongDJetBound G Z d c) := by
  obtain ⟨hqs, hqb⟩ := hessianQuotient_bound_from_metric_height_jets hg hU hz hG hZ hd hc hgB hzB hdet hyy
  have hqN := heightQuotientJetBound_nonneg hG hZ hd hc
  have hΓN := christoffelJetBound_nonneg hG hd
  have hΓs (a b : Fin 2) := christoffel_contDiffOn hg hU i a b
  have hΓb (a b : Fin 2) := christoffel_coordinate_bound hg hU hG hd hgB hdet i a b
  have hqb' : CoordinateBound (hessianQuotient g z) U 3 (heightQuotientJetBound G Z d c) := hqb
  have hqΓ := CoordinateBound.mul_through_three hqs (hΓs 0 1) hU hqN hΓN hqb' (hΓb 0 1)
  have htwice := CoordinateBound.const_mul (hqs.mul (hΓs 0 1)) hU hqΓ (2 : ℝ)
  have hqsq : CoordinateBound (fun p => (hessianQuotient g z p)^2) U 3
      (8 * (heightQuotientJetBound G Z d c)^2) := by
    convert CoordinateBound.mul_through_three hqs hqs hU hqN hqN hqb' hqb' using 1 <;>
      simp only [pow_two, mul_assoc]
  have hthird := CoordinateBound.mul_through_three (hqs.pow 2) (hΓs 1 1) hU
    (by positivity : 0 ≤ 8 * (heightQuotientJetBound G Z d c)^2) hΓN hqsq (hΓb 1 1)
  have hb := CoordinateBound.add
    ((hΓs 0 0).sub (contDiffOn_const.mul (hqs.mul (hΓs 0 1))))
    ((hqs.pow 2).mul (hΓs 1 1)) hU
    (CoordinateBound.sub (hΓs 0 0) (contDiffOn_const.mul (hqs.mul (hΓs 0 1))) hU (hΓb 0 0) htwice) hthird
  have hconstant : christoffelJetBound G d + |(2 : ℝ)| *
      (8 * heightQuotientJetBound G Z d c * christoffelJetBound G d) +
      8 * (8 * (heightQuotientJetBound G Z d c)^2) * christoffelJetBound G d =
      heightAlongDJetBound G Z d c := by norm_num [heightAlongDJetBound]; ring
  rw [hconstant] at hb
  apply CoordinateBound.congr_on hU hb
  intro p hp
  change christoffelAlongD g p (hessianQuotient g z p) i =
    christoffel g i 0 0 p - 2 * (hessianQuotient g z p * christoffel g i 0 1 p) +
      (hessianQuotient g z p)^2 * christoffel g i 1 1 p
  rw [christoffelAlongD_eq hg hU hp]
  ring

theorem heightPFirst_coordinate_bound_one
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) (i : Fin 2) :
    CoordinateBound (heightPFirst g z i) U 1 (heightPFirstBound G Z d c) := by
  have hne := LowQuotient.denominator_ne_zero hc hyy
  have hH := hessianJetBound_nonneg hG hZ hd
  have hΓ := christoffelJetBound_nonneg hG hd
  have hD := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  have hJ := heightEnergyFirstQuotientBound_nonneg hG hZ hd hc
  have hK := curvatureFirstBound_nonneg hG hd
  have hsH := covHessian_contDiffOn hg hU hz 1 1
  have hsJ := height_jetEnergy_first_contDiffOn hg hU hz i
  have hsG := darbouxG_contDiffOn hg hU hz hne
  have hsΓ := christoffel_contDiffOn hg hU i 1 1
  have hJB := height_jetEnergy_first_coordinate_bound hg hU hz hG hZ
    (fun a b => (hgB a b).mono (by norm_num) le_rfl) (hzB.mono (by norm_num) le_rfl) i
  have hHB := covHessian_coordinate_bound hg hU hz hG hZ hd hgB hzB hdet 1 1
  let N := 32 * G * Z + hessianJetBound G Z d
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hJN : 32 * G * Z ≤ N := by dsimp [N]; linarith
  have hHN : hessianJetBound G Z d ≤ N := by dsimp [N]; nlinarith [mul_nonneg hG hZ]
  have hdiv : CoordinateBound (fun p => coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) /
      covHessian g z p 1 1) U 3 (heightEnergyFirstQuotientBound G Z d c) := by
    intro ds hds p hp
    exact LowQuotient.quotient_bound_through_three hsJ hsH hU hN hc
      (hJB.mono le_rfl hJN) (hHB.mono le_rfl hHN) hyy ds hds hp
  have hGΓ := CoordinateBound.mul_through_three hsG hsΓ hU hD hΓ
    (darbouxG_coordinate_bound hg hU hz hG hZ hd hc hgB hzB hdet hyy)
    (christoffel_coordinate_bound hg hU hG hd hgB hdet i 1 1)
  have hsdiv := hsJ.div hsH hne
  have hbracket := CoordinateBound.add hsdiv (hsG.mul hsΓ) hU hdiv hGΓ
  have hmul := CoordinateBound.mul_through_one (gaussianCurvature_contDiffOn hg hU)
    (hsdiv.add (hsG.mul hsΓ)) hU hK
    (by positivity : 0 ≤ heightEnergyFirstQuotientBound G Z d c + 8 * darbouxGJetBound G Z d c * christoffelJetBound G d)
    (gaussianCurvature_coordinate_bound_one hg hU hG hd hgB hdet)
    (hbracket.mono (by norm_num) le_rfl)
  have hbs := height_christoffelAlongD_contDiffOn hg hU hz hne i
  have hb := CoordinateBound.add hbs ((gaussianCurvature_contDiffOn hg hU).mul (hsdiv.add (hsG.mul hsΓ))) hU
    ((height_christoffelAlongD_coordinate_bound hg hU hz hG hZ hd hc hgB hzB hdet hyy i).mono
      (by norm_num) le_rfl) hmul
  apply CoordinateBound.congr_on hU hb
  intro p hp
  change heightPFirst g z i p = christoffelAlongD g p (hessianQuotient g z p) i +
    gaussianCurvature g p *
      (coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) / covHessian g z p 1 1 +
        darbouxG g z p * christoffel g i 1 1 p)
  rw [heightPFirst_eq hg hU hp (hne p hp) i]
  unfold darbouxG
  simp only [div_eq_mul_inv]
  ring

end SmoothLocal.Geometry

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

section HeightWords
variable {Y : ℝ → ℝ → ℝ}
variable (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
include hY

theorem capFlowHeight_partial_one_eq {p : Coord} (hp : p ∈ capChartDomain) :
    coordPartial 1 (capFlowHeight Y) p = initialFlowDerivative Y (p 0, p 1) :=
  (capFlowHeight_hasDerivAt_initial hY hp).deriv.symm

end HeightWords

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

theorem exists_open_low_height_coefficients
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) :
    ∃ V : Set Coord, IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      (∀ p ∈ V, covHessian g z p 1 1 ≠ 0) ∧
      CoordinateBound (hessianQuotient g z) modelSquare 3 (heightQuotientJetBound G Z d c) ∧
      CoordinateBound (heightEnergy g z) modelSquare 3 (heightEnergyJetBound G Z) ∧
      CoordinateBound (darbouxG g z) modelSquare 3 (darbouxGJetBound G Z d c) ∧
      (∀ i : Fin 2, CoordinateBound (heightPFirst g z i) modelSquare 1 (heightPFirstBound G Z d c)) ∧
      (∀ k i j : Fin 2, CoordinateBound (christoffel g k i j) modelSquare 3 (christoffelJetBound G d)) := by
  obtain ⟨V, hV, hSV, hVU, hVne, _, hqB⟩ :=
    exists_open_quotient_domain_with_closed_low_bounds hg hU hSU hz hG hZ hd hc hgB hzB hdet hyy
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun i j => (hg.1 i j).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  have hgV : SmoothPositiveOn g V :=
    ⟨fun i j => (hg.1 i j).mono hVU, fun p hp => hg.2 p (hVU hp)⟩
  have hgBI (i j : Fin 2) := (hgB i j).restrict_domain interior_subset
  have hzBI := hzB.restrict_domain interior_subset
  have hdI (p : Coord) (hp : p ∈ interior modelSquare) := hdet p (interior_subset hp)
  have hyyI (p : Coord) (hp : p ∈ interior modelSquare) := hyy p (interior_subset hp)
  refine ⟨V, hV, hSV, hVU, hVne, hqB, ?_, ?_, ?_, ?_⟩
  · apply CoordinateBound.of_modelSquare_interior (heightEnergy_contDiffOn hg hU hz) hU hSU
    exact heightEnergy_coordinate_bound hgI isOpen_interior (hz.mono hIU) hG hZ
      (fun i j => (hgBI i j).mono (by norm_num) le_rfl) (hzBI.mono (by norm_num) le_rfl)
  · apply CoordinateBound.of_modelSquare_interior
      (darbouxG_contDiffOn hgV hV (hz.mono hVU) hVne) hV hSV
    exact darbouxG_coordinate_bound hgI isOpen_interior (hz.mono hIU) hG hZ hd hc hgBI hzBI hdI hyyI
  · intro i
    apply CoordinateBound.of_modelSquare_interior
      (heightPFirst_contDiffOn hgV hV (hz.mono hVU) hVne i) hV hSV
    exact heightPFirst_coordinate_bound_one hgI isOpen_interior (hz.mono hIU) hG hZ hd hc hgBI hzBI hdI hyyI i
  · intro k i j
    apply CoordinateBound.of_modelSquare_interior (christoffel_contDiffOn hg hU k i j) hU hSU
    exact christoffel_coordinate_bound hgI isOpen_interior hG hd hgBI hdI k i j

theorem curvatureDriftError_bound_original_data
    {g : MetricField} {z : Coord → ℝ} {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hEB : CoordinateBound (heightEnergy g z) modelSquare 3 (heightEnergyJetBound G Z))
    (hHB : CoordinateBound (fun p => covHessian g z p 1 1) modelSquare 3 (hessianJetBound G Z d))
    (hΓB : ∀ k i j : Fin 2, CoordinateBound (christoffel g k i j) modelSquare 3 (christoffelJetBound G d))
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ) / 100)
    {p : Coord} (hp : p ∈ modelSquare) :
    |curvatureDriftError g z p| ≤ heightDriftErrorBound G Z d c := by
  have ht : |connectionTraceY g p| ≤ 2 * christoffelJetBound G d := by
    exact ((abs_add_le _ _).trans
      (add_le_add (hΓB 0 0 1 [] (by norm_num) p hp) (hΓB 1 1 1 [] (by norm_num) p hp))).trans
        (le_of_eq (by ring))
  exact curvatureDriftError_bound_from_low_data g z p c (heightEnergyJetBound G Z)
    (hessianJetBound G Z d) (2 * christoffelJetBound G d) (G + Z)
    hc (hyy p hp) (hEB [] (by norm_num) p hp) (hHB [1] (by norm_num) p hp) ht
    (fun i j => (hgB i j [] (by norm_num) p hp).trans (by linarith))
    (fun i => (hzB [i] (by norm_num) p hp).trans (by linarith)) (hsmall p hp)

end SmoothLocal.Geometry

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

theorem negative_over_cube_partial {f v : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (hv : DifferentiableAt ℝ v p) (hne : v p ≠ 0) (i : Fin 2) :
    coordPartial i (fun x => -f x / (v x)^3) p =
      -coordPartial i f p / (v p)^3 + 3 * f p * coordPartial i v p / (v p)^4 := by
  have hn : DifferentiableAt ℝ (fun x => -f x) p := hf.neg
  have hp : DifferentiableAt ℝ (fun x => (v x)^3) p := hv.pow 3
  rw [coordPartial_div hn hp (pow_ne_zero 3 hne) i]
  have hneg : coordPartial i (fun x => -f x) p = -coordPartial i f p := by simp [coordPartial]
  have hpow : coordPartial i (fun x => (v x)^3) p = 3 * (v p)^2 * coordPartial i v p := by
    unfold coordPartial
    rw [(hv.hasFDerivAt.pow 3).fderiv]
    norm_num [smul_apply, smul_eq_mul]
  rw [hneg, hpow]
  field_simp [hne]
  ring

theorem capChartRho_partial {Y : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (capFlowHeight Y) capChartDomain)
    {p : Coord} (hp : p ∈ capChartDomain)
    (hpos : 0 < coordPartial 1 (capFlowHeight Y) p) (i : Fin 2) :
    coordPartial i (capChartRho Y) p =
      -coordPartial i (coordPartial 1 (capFlowHeight Y)) p /
        (coordPartial 1 (capFlowHeight Y) p)^2 := by
  have hV := ((partial_contDiffOn hF capChartDomain_isOpen 1).contDiffAt
    (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  change coordPartial i (fun x => (1 : ℝ) / coordPartial 1 (capFlowHeight Y) x) p = _
  rw [coordPartial_div (differentiableAt_const (1 : ℝ)) hV hpos.ne' i]
  simp [coordPartial]

theorem capChartSigma_partial {Y : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (capFlowHeight Y) capChartDomain)
    {p : Coord} (hp : p ∈ capChartDomain)
    (hpos : 0 < coordPartial 1 (capFlowHeight Y) p) (i : Fin 2) :
    coordPartial i (capChartSigma Y) p =
      -coordPartial i (coordPartial 1 (coordPartial 1 (capFlowHeight Y))) p /
        (coordPartial 1 (capFlowHeight Y) p)^3 +
      3 * coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p *
        coordPartial i (coordPartial 1 (capFlowHeight Y)) p /
        (coordPartial 1 (capFlowHeight Y) p)^4 := by
  have hV := partial_contDiffOn hF capChartDomain_isOpen 1
  have hW := partial_contDiffOn hV capChartDomain_isOpen 1
  exact negative_over_cube_partial
    ((hW.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp))
    ((hV.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)) hpos.ne' i

theorem capReciprocal_bounds_of_jets {Y : ℝ → ℝ → ℝ} {C c : ℝ}
    (hF : ContDiffOn ℝ ∞ (capFlowHeight Y) capChartDomain)
    (hC : 0 ≤ C) (hc : 0 < c)
    (hFB : CoordinateBound (capFlowHeight Y) capChartDomain 3 C)
    (hVlower : ∀ p ∈ capChartDomain, c ≤ coordPartial 1 (capFlowHeight Y) p)
    {p : Coord} (hp : p ∈ capChartDomain) :
    0 < capChartRho Y p ∧ |capChartRho Y p| ≤ 1 / c ∧
    (∀ i : Fin 2, |coordPartial i (capChartRho Y) p| ≤ C / c^2) ∧
    |capChartSigma Y p| ≤ C / c^3 ∧
    (∀ i : Fin 2, |coordPartial i (capChartSigma Y) p| ≤ C / c^3 + 3 * C^2 / c^4) := by
  have hVp : 0 < coordPartial 1 (capFlowHeight Y) p := hc.trans_le (hVlower p hp)
  have hpow (n : ℕ) : c^n ≤ |(coordPartial 1 (capFlowHeight Y) p)^n| := by
    rw [abs_pow, abs_of_pos hVp]
    exact pow_le_pow_left₀ hc.le (hVlower p hp) n
  have hW : |coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p| ≤ C :=
    hFB [1, 1] (by norm_num) p hp
  have hVi (i : Fin 2) : |coordPartial i (coordPartial 1 (capFlowHeight Y)) p| ≤ C :=
    hFB [i, 1] (by norm_num) p hp
  have hWi (i : Fin 2) : |coordPartial i (coordPartial 1 (coordPartial 1 (capFlowHeight Y))) p| ≤ C :=
    hFB [i, 1, 1] (by norm_num) p hp
  refine ⟨one_div_pos.mpr hVp, ?_, ?_, ?_, ?_⟩
  · exact LowQuotient.abs_div_bound (by norm_num) (by norm_num : |(1 : ℝ)| ≤ 1) hc
      (by simpa only [abs_of_pos hVp] using hVlower p hp)
  · intro i
    rw [capChartRho_partial hF hp hVp i]
    exact LowQuotient.abs_div_bound hC (by simpa only [abs_neg] using hVi i)
      (pow_pos hc 2) (hpow 2)
  · exact LowQuotient.abs_div_bound hC (by simpa only [abs_neg] using hW)
      (pow_pos hc 3) (hpow 3)
  · intro i
    rw [capChartSigma_partial hF hp hVp i]
    have hfirst :
        |-coordPartial i (coordPartial 1 (coordPartial 1 (capFlowHeight Y))) p /
          (coordPartial 1 (capFlowHeight Y) p)^3| ≤ C / c^3 :=
      LowQuotient.abs_div_bound hC (by simpa only [abs_neg] using hWi i)
        (pow_pos hc 3) (hpow 3)
    have hnum : |3 * coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p *
        coordPartial i (coordPartial 1 (capFlowHeight Y)) p| ≤ 3 * C^2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      calc
        _ = 3 * (|coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p| *
            |coordPartial i (coordPartial 1 (capFlowHeight Y)) p|) := by ring
        _ ≤ 3 * (C * C) := mul_le_mul_of_nonneg_left
          (mul_le_mul hW (hVi i) (abs_nonneg _) hC) (by norm_num)
        _ = 3 * C^2 := by ring
    have hsecond := LowQuotient.abs_div_bound (by positivity) hnum (pow_pos hc 4) (hpow 4)
    exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
variable (hM : 0 ≤ M)
variable (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
variable (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
variable (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
variable (hq3 : ∀ i j k : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j (coordPartial k q)) p| ≤ M)
include hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3

theorem capReciprocal_bounds_from_q {p : Coord} (hp : p ∈ capChartDomain) :
    0 < capChartRho Y p ∧ |capChartRho Y p| ≤ 1 / Real.exp (-2 * M) ∧
    (∀ i : Fin 2, |coordPartial i (capChartRho Y) p| ≤ flowCoordinateBound M / (Real.exp (-2 * M))^2) ∧
    |capChartSigma Y p| ≤ flowCoordinateBound M / (Real.exp (-2 * M))^3 ∧
    (∀ i : Fin 2, |coordPartial i (capChartSigma Y) p| ≤
      flowCoordinateBound M / (Real.exp (-2 * M))^3 +
        3 * (flowCoordinateBound M)^2 / (Real.exp (-2 * M))^4) := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hVlower (x : Coord) (hx : x ∈ capChartDomain) :
      Real.exp (-2 * M) ≤ coordPartial 1 (capFlowHeight Y) x := by
    rw [capFlowHeight_partial_one_eq hs hx]
    exact (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hx.2 hx.1).1
  exact capReciprocal_bounds_of_jets (capFlowHeight_contDiffOn hs) (flowCoordinateBound_nonneg hM)
    (Real.exp_pos _) (capFlowHeight_coordinate_bound hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3)
    hVlower hp

end ActualFlow
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

theorem capPullback_bound_one {u : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {A F : ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U)
    (hmapS : MapsTo (capChart Y) capChartDomain modelSquare)
    (hA : 0 ≤ A) (hF : 0 ≤ F)
    (huB : CoordinateBound u modelSquare 1 A)
    (hFB : CoordinateBound (capFlowHeight Y) capChartDomain 3 F) :
    CoordinateBound (capPullback Y u) capChartDomain 1 (A * (1 + F)) := by
  intro ds hds p hp
  have hv : |u (capChart Y p)| ≤ A := huB [] (by norm_num) _ (hmapS hp)
  have hdu (i : Fin 2) : |coordPartial i u (capChart Y p)| ≤ A := huB [i] (by norm_num) _ (hmapS hp)
  have hdf (i : Fin 2) : |coordPartial i (capFlowHeight Y) p| ≤ F := hFB [i] (by norm_num) p hp
  cases ds with
  | nil => exact hv.trans (by nlinarith [mul_nonneg hA hF])
  | cons i ds =>
    cases ds with
    | nil =>
      change |coordPartial i (capPullback Y u) p| ≤ A * (1 + F)
      rw [capPullback_partial hY hp ((hu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp)) i]
      have h0 : |if i = 0 then coordPartial 0 u (capChart Y p) else 0| ≤ A := by
        split_ifs
        · exact hdu 0
        · simpa only [abs_zero] using hA
      have h1 : |coordPartial 1 u (capChart Y p) * coordPartial i (capFlowHeight Y) p| ≤ A * F := by
        rw [abs_mul]
        exact mul_le_mul (hdu 1) (hdf i) (abs_nonneg _) hA
      exact ((abs_add_le _ _).trans (add_le_add h0 h1)).trans (le_of_eq (by ring))
    | cons _ ds => simp only [List.length_cons] at hds; omega

theorem heightOriginalB_bound_one {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {P Q : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hne : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hPB : CoordinateBound (heightPFirst g z 0) modelSquare 1 P)
    (hqB : CoordinateBound (hessianQuotient g z) modelSquare 3 Q) (ell : ℕ) :
    CoordinateBound (heightOriginalB g z ell) modelSquare 1 (P + 2 * (ell : ℝ) * Q) := by
  have hI : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hP := heightPFirst_contDiffOn hg hU hz hne 0
  have hq := hessianQuotient_contDiffOn hg hU hz hne
  have hqy := partial_contDiffOn hq hU 1
  have hqyB : CoordinateBound (coordPartial 1 (hessianQuotient g z)) modelSquare 1 Q :=
    (hqB.mono (by norm_num : 2 ≤ 3) le_rfl).partial_bound 1
  have ht := CoordinateBound.const_mul (hqy.mono hI) isOpen_interior
    (hqyB.restrict_domain interior_subset) (2 * (ell : ℝ))
  have hb := CoordinateBound.sub (hP.neg.mono hI) (contDiffOn_const.mul (hqy.mono hI)) isOpen_interior
    (CoordinateBound.neg (hP.mono hI) isOpen_interior (hPB.restrict_domain interior_subset)) ht
  have hc : |2 * (ell : ℝ)| = 2 * (ell : ℝ) := abs_of_nonneg (by positivity)
  rw [hc] at hb
  exact CoordinateBound.of_modelSquare_interior (heightOriginalB_contDiffOn hg hU hz hne ell) hU hSU hb

theorem capChartRho_lower_from_q
    {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hM : 0 ≤ M) (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    {p : Coord} (hp : p ∈ capChartDomain) : 1 / Real.exp (2 * M) ≤ capChartRho Y p := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hpos := cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hp.2 hp.1
  have hupper := (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hq1 hp.2 hp.1).2
  unfold capChartRho
  rw [capFlowHeight_partial_one_eq hs hp]
  apply (le_div_iff₀ hpos).mpr
  calc
    _ ≤ (1 / Real.exp (2 * M)) * Real.exp (2 * M) := mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = 1 := one_div_mul_cancel (Real.exp_ne_zero _)

theorem heightChartRemainder_bound_of_low_coefficients
    (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : Coord) (ell : ℕ)
    {DE DG SG lowerG RL : ℝ} (hDE : 0 ≤ DE) (hDG : 0 ≤ DG) (hSG : 0 ≤ SG)
    (hGL : 0 < lowerG) (hRL : 0 < RL)
    (herror : |curvatureDriftError g z (capChart Y p)| ≤ DE)
    (hGy : |coordPartial 1 (darbouxG g z) (capChart Y p)| ≤ DG)
    (hG : lowerG ≤ darbouxG g z (capChart Y p))
    (hrho : RL ≤ capChartRho Y p) (hsigma : |capChartSigma Y p| ≤ SG) :
    |heightChartRemainder g z Y ell p| ≤
      (DE + DG) / (lowerG * RL) + (2 * (ell : ℝ) + 1) * SG / RL^2 := by
  have hGpos : 0 < darbouxG g z (capChart Y p) := hGL.trans_le hG
  have hrhopos : 0 < capChartRho Y p := hRL.trans_le hrho
  have hden : lowerG * RL ≤ |darbouxG g z (capChart Y p) * capChartRho Y p| := by
    rw [abs_of_pos (mul_pos hGpos hrhopos)]
    exact mul_le_mul hG hrho hRL.le hGpos.le
  have hden2 : RL^2 ≤ |(capChartRho Y p)^2| := by
    rw [abs_pow, abs_of_pos hrhopos]
    exact pow_le_pow_left₀ hRL.le hrho 2
  have hnum := (abs_sub _ _).trans (add_le_add herror hGy)
  have hfirst := LowQuotient.abs_div_bound (add_nonneg hDE hDG) hnum (mul_pos hGL hRL) hden
  have hnum2 : |(2 * (ell : ℝ) + 1) * capChartSigma Y p| ≤ (2 * (ell : ℝ) + 1) * SG := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (ell : ℝ) + 1)]
    exact mul_le_mul_of_nonneg_left hsigma (by positivity)
  have hsecond := LowQuotient.abs_div_bound (by positivity) hnum2 (pow_pos hRL 2) hden2
  exact (abs_sub _ _).trans (add_le_add hfirst hsecond)

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

theorem exists_height_flow_uniform_coefficients
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy g z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ) / 100)
    (hD : ∀ p ∈ modelSquare, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    ∃ Y : ℝ → ℝ → ℝ,
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, |Y s t - s| ≤ (1 : ℝ) / 50) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) ∧
      (∀ p ∈ capChartDomain,
        0 < capChartRho Y p ∧
        1 / Real.exp (2 * heightQuotientJetBound G Z d c) ≤ capChartRho Y p ∧
        capChartRho Y p ≤ 1 / Real.exp (-2 * heightQuotientJetBound G Z d c)) ∧
      ContDiffOn ℝ ∞ (heightChartG1 g z Y) capChartDomain ∧
      CoordinateBound (heightChartG1 g z Y) capChartDomain 1 (heightG1JetBound G Z d c) ∧
      (∀ p ∈ capChartDomain, heightG1Lower G Z d c e0 ≤ heightChartG1 g z Y p) ∧
      (∀ ell : ℕ,
        ContDiffOn ℝ ∞ (heightChartB g z Y ell) capChartDomain ∧
        CoordinateBound (heightChartB g z Y ell) capChartDomain 1 (heightBJetBound G Z d c ell) ∧
        ContDiffOn ℝ ∞ (heightChartRemainder g z Y ell) capChartDomain ∧
        ∀ p ∈ capChartDomain,
          |heightChartRemainder g z Y ell p| ≤ heightRemainderBound G Z d c e0 ell ∧
          heightChartC g z Y ell p = ((ell : ℝ) + 1) * coordPartial 1 (heightChartA g z Y) p +
            heightChartA g z Y p * heightChartRemainder g z Y ell p) := by
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hM
  have hH := hessianJetBound_nonneg hG hZ hd
  have hDG := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  have hP := heightPFirstBound_nonneg hG hZ hd hc
  have hDE := heightDriftErrorBound_nonneg hG hZ hd hc
  obtain ⟨V, hV, hSV, hVU, hVne, hqB, hEB, hGB, hPB, hΓB⟩ :=
    exists_open_low_height_coefficients hg hU hSU hz hG hZ hd hc hgB hzB hdet hyy
  have hgV : SmoothPositiveOn g V :=
    ⟨fun i j => (hg.1 i j).mono hVU, fun p hp => hg.2 p (hVU hp)⟩
  have hzV := hz.mono hVU
  have hq := hessianQuotient_contDiffOn hgV hV hzV hVne
  have hGs := darbouxG_contDiffOn hgV hV hzV hVne
  have hq1 (i : Fin 2) (p : Coord) (hp : p ∈ modelSquare) : |coordPartial i (hessianQuotient g z) p| ≤ M :=
    hqB [i] (by norm_num) p hp
  have hq2 (i j : Fin 2) (p : Coord) (hp : p ∈ modelSquare) :
      |coordPartial i (coordPartial j (hessianQuotient g z)) p| ≤ M := hqB [i, j] (by norm_num) p hp
  have hq3 (i j k : Fin 2) (p : Coord) (hp : p ∈ modelSquare) :
      |coordPartial i (coordPartial j (coordPartial k (hessianQuotient g z))) p| ≤ M :=
    hqB [i, j, k] (by norm_num) p hp
  obtain ⟨Y, hY, _, hstart, hode, _, hdisp50, hrange, _⟩ := exists_cap_flow hq hV hSV hsmall
  have hconf (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) (t : ℝ) (ht : t ∈ Icc (-2 : ℝ) 2) :
      Y s t ∈ Icc (-3 : ℝ) 3 := abs_le.mp ((hrange s hs t ht).1.trans (by norm_num))
  have hYs := cap_flow_joint_contDiffOn hq hV hSV hY hconf hstart hode
  have hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s := fun s hs t ht =>
    cap_flow_initial_deriv_pos hq hV hSV hY hconf hstart hode hs ht
  have hdisp' (p : Coord) (hp : p ∈ capChartDomain) : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50 :=
    hdisp50 (p 1) ⟨hp.2.1.le, hp.2.2.le⟩ (p 0) ⟨hp.1.1.le, hp.1.2.le⟩
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp' p hp)
  have hmapS : MapsTo (capChart Y) capChartDomain modelSquare := fun p hp => modelOpenSquare_subset (hmapO hp)
  have hmapV : MapsTo (capChart Y) capChartDomain V := fun p hp => hSV (hmapS hp)
  have hFB := capFlowHeight_coordinate_bound hq hV hSV hY hconf hstart hode hM hsmall hq1 hq2 hq3
  have hrec (p : Coord) (hp : p ∈ capChartDomain) :=
    capReciprocal_bounds_from_q hq hV hSV hY hconf hstart hode hM hsmall hq1 hq2 hq3 hp
  have hrhoL (p : Coord) (hp : p ∈ capChartDomain) : 1 / Real.exp (2 * M) ≤ capChartRho Y p :=
    capChartRho_lower_from_q hq hV hSV hY hconf hstart hode hM (hq1 1) hp
  have hrhoJ : 0 ≤ flowRhoJetBound M := by dsimp [flowRhoJetBound]; positivity
  have hrhoB : CoordinateBound (capChartRho Y) capChartDomain 1 (flowRhoJetBound M) := by
    intro ds hds p hp
    cases ds with
    | nil =>
      exact (hrec p hp).2.1.trans (by
        dsimp [flowRhoJetBound]
        have hterm : 0 ≤ flowCoordinateBound M / (Real.exp (-2 * M))^2 := by positivity
        linarith)
    | cons i ds =>
      cases ds with
      | nil =>
        exact ((hrec p hp).2.2.1 i).trans (by
          dsimp [flowRhoJetBound]
          have hterm : 0 ≤ 1 / Real.exp (-2 * M) := by positivity
          linarith)
      | cons _ ds => simp only [List.length_cons] at hds; omega
  have hrhos := capChartRho_contDiffOn hYs hvar
  have hGrho := capPullback_bound_one hYs hGs hV hmapV hmapS hDG hF
    (hGB.mono (by norm_num) le_rfl) hFB
  have hG1B := CoordinateBound.mul_through_one (capPullback_contDiffOn hYs hGs hmapV)
    (hrhos.mul hrhos) capChartDomain_isOpen (mul_nonneg hDG (by positivity))
    (by positivity : 0 ≤ 2 * flowRhoJetBound M * flowRhoJetBound M) hGrho
    (CoordinateBound.mul_through_one hrhos hrhos capChartDomain_isOpen hrhoJ hrhoJ hrhoB hrhoB)
  have hHB := covHessian_coordinate_bound_closed_square hg hU hSU hz hG hZ hd hgB hzB hdet 1 1
  have hGfloor (p : Coord) (hp : p ∈ capChartDomain) :
      e0 / (1 + hessianJetBound G Z d)^2 ≤ darbouxG g z (capChart Y p) :=
    darbouxG_lower_of_energy_floor g z _ he0 (hEfloor _ (hmapS hp)) hH
      (hHB [] (by norm_num) _ (hmapS hp)) (hVne _ (hmapV hp))
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU, fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hD0 := fun p (hp : p ∈ modelOpenSquare) => hD p (modelOpenSquare_subset hp)
  have hE0 := fun p (hp : p ∈ modelOpenSquare) => he0.trans_le (hEfloor p (modelOpenSquare_subset hp))
  have hyy0 := fun p (hp : p ∈ modelOpenSquare) => hVne p (hSV (modelOpenSquare_subset hp))
  refine ⟨Y, capChart_contDiffOn hYs, hY, hYs, hvar, hstart, hode, hconf, hdisp50, hdisp', ?_,
    (capPullback_contDiffOn hYs hGs hmapV).mul (hrhos.pow 2), ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨(hrec p hp).1, hrhoL p hp, (le_abs_self _).trans (hrec p hp).2.1⟩
  · convert hG1B using 1 <;> first
      | (funext p; simp only [heightChartG1, pow_two])
      | (dsimp [heightG1JetBound, M]; ring)
  · intro p hp
    have hGL : 0 < e0 / (1 + hessianJetBound G Z d)^2 := by positivity
    have hGpos := hGL.trans_le (hGfloor p hp)
    have hsquare := pow_le_pow_left₀ (show 0 ≤ 1 / Real.exp (2 * M) by positivity) (hrhoL p hp) 2
    exact mul_le_mul (hGfloor p hp) hsquare (sq_nonneg _) hGpos.le
  · intro ell
    have hBB := heightOriginalB_bound_one hgV hV hSV hzV hVne (hPB 0) hqB ell
    refine ⟨heightChartB_contDiffOn hgV hV hzV hVne hYs hmapV ell, ?_,
      heightChartRemainder_contDiffOn hgO modelOpenSquare_isOpen hzO hyy0 hE0 hYs hvar hmapO ell, ?_⟩
    · exact capPullback_bound_one hYs (heightOriginalB_contDiffOn hgV hV hzV hVne ell) hV hmapV hmapS
        (by positivity : 0 ≤ heightPFirstBound G Z d c + 2 * (ell : ℝ) * M) hF hBB hFB
    · intro p hp
      refine ⟨?_, heightChartC_factor hgO modelOpenSquare_isOpen hzO hD0 hyy0 hE0 hYs hvar hmapO hp ell⟩
      exact heightChartRemainder_bound_of_low_coefficients g z Y p ell hDE hDG
        (show 0 ≤ flowCoordinateBound M / (Real.exp (-2 * M))^3 by positivity)
        (show 0 < e0 / (1 + hessianJetBound G Z d)^2 by positivity)
        (show 0 < 1 / Real.exp (2 * M) by positivity)
        (curvatureDriftError_bound_original_data hG hZ hc hgB hzB hEB hHB hΓB hyy hsmall (hmapS hp))
        (hGB [1] (by norm_num) _ (hmapS hp)) (hGfloor p hp) (hrhoL p hp) (hrec p hp).2.2.2.1

end SmoothLocal.Flow

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Flow.exists_height_flow_uniform_coefficients := @OAI.SmoothLocal.Flow.exists_height_flow_uniform_coefficients
