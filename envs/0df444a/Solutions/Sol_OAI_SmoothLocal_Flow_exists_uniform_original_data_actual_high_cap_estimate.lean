-- Prove2me | solution 1 for OAI.SmoothLocal.Flow.exists_uniform_original_data_actual_high_cap_estimate
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:13:21.365666+00:00
-- url     : https://prove2.me/submissions/1a0461d7-3d13-407e-9b3f-fbae38e441a9

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport
import Theorems.Thm_OAI_SmoothLocal_Weighted_primitive_directed_farnegative_coercivity
import Theorems.Thm_OAI_SmoothLocal_Flow_patch_actual_directed_near_coercivity
import Theorems.Thm_OAI_SmoothLocal_Flow_exists_height_flow_uniform_coefficients
import Theorems.Thm_OAI_SmoothLocal_Flow_actual_cap_integrated_overlap_estimate

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
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

variable {I : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem directedWeight_differentiableAt
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    DifferentiableAt ℝ (directedWeight b lambda I) p := by
  have hD := (hasFDerivAt_const (𝕜 := ℝ) b p).sub (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hPhi := ((hasFDerivAt_apply (𝕜 := ℝ) 1 p).const_mul (-lambda)).add hI.hasFDerivAt
  have hd := (hD.pow 8).fun_mul hPhi.exp
  simp only [Pi.add_def, Pi.sub_def] at hd
  exact hd.differentiableAt

theorem directedWeight_partial
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) (i : Fin 2) :
    coordPartial i (directedWeight b lambda I) p =
      -8 * (edgeDistance b p) ^ 7 * (if (1 : Fin 2) = i then 1 else 0) *
          Real.exp (weightPhase lambda I p) +
        directedWeight b lambda I p *
          (coordPartial i I p - lambda * (if (1 : Fin 2) = i then 1 else 0)) := by
  have hD := (hasFDerivAt_const (𝕜 := ℝ) b p).sub (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hPhi := ((hasFDerivAt_apply (𝕜 := ℝ) 1 p).const_mul (-lambda)).add hI.hasFDerivAt
  have hd := (hD.pow 8).fun_mul hPhi.exp
  simp only [Pi.add_def, Pi.sub_def] at hd
  change fderiv ℝ (fun q : Coord => (b - q 1) ^ 8 * Real.exp (-lambda * q 1 + I q))
    p (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;>
    simp [edgeDistance, directedWeight, weightPhase, coordPartial] <;> ring

theorem directedWeight_contDiffOn (b lambda : ℝ) (hI : ContDiffOn ℝ ∞ I U) :
    ContDiffOn ℝ ∞ (directedWeight b lambda I) U := by
  have hy : ContDiffOn ℝ ∞ (fun p : Coord => p 1) U :=
    contDiffOn_apply ℝ ℝ 1 U
  have hD : ContDiffOn ℝ ∞ (fun p : Coord => b - p 1) U :=
    contDiffOn_const.sub hy
  have hLambda : ContDiffOn ℝ ∞ (fun _ : Coord => -lambda) U := contDiffOn_const
  have hPhi : ContDiffOn ℝ ∞ (fun p : Coord => -lambda * p 1 + I p) U :=
    (hLambda.mul hy).add hI
  exact (hD.pow 8).mul hPhi.exp

theorem directedWeight_edge_zero (b lambda : ℝ) (I : Coord → ℝ) (p : Coord)
    (hp : p 1 = b) : directedWeight b lambda I p = 0 := by
  simp [directedWeight, edgeDistance, hp]

theorem directedWeight_partial_edge_zero
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) (hp : p 1 = b) (i : Fin 2) :
    coordPartial i (directedWeight b lambda I) p = 0 := by
  rw [directedWeight_partial b lambda hI i]
  simp [edgeDistance, directedWeight, hp]

theorem directedM_differentiableAt
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    DifferentiableAt ℝ (directedM b lambda I) p :=
  (directedWeight_differentiableAt b lambda hI).neg

theorem directedN_differentiableAt
    (b lambda epsilon : ℝ) (hI : DifferentiableAt ℝ I p) :
    DifferentiableAt ℝ (directedN b lambda epsilon I) p :=
  ((differentiableAt_apply (𝕜 := ℝ) 0 p).const_mul epsilon).mul
    (directedWeight_differentiableAt b lambda hI)

theorem directedM_partial (b lambda : ℝ) (i : Fin 2) :
    coordPartial i (directedM b lambda I) p =
      -coordPartial i (directedWeight b lambda I) p := by
  change fderiv ℝ (fun q : Coord => -directedWeight b lambda I q) p (Pi.single i 1) =
    -fderiv ℝ (directedWeight b lambda I) p (Pi.single i 1)
  simp only [fderiv_fun_neg, neg_apply]

theorem directedN_partial
    (b lambda epsilon : ℝ) (hI : DifferentiableAt ℝ I p) (i : Fin 2) :
    coordPartial i (directedN b lambda epsilon I) p =
      epsilon * (if (0 : Fin 2) = i then 1 else 0) * directedWeight b lambda I p +
        epsilon * p 0 * coordPartial i (directedWeight b lambda I) p := by
  have hd := ((hasFDerivAt_apply (𝕜 := ℝ) 0 p).const_mul epsilon).fun_mul
    (directedWeight_differentiableAt b lambda hI).hasFDerivAt
  change fderiv ℝ (fun q : Coord => epsilon * q 0 * directedWeight b lambda I q)
    p (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;> simp [coordPartial]
  ring

theorem directed_mn_edge_zero
    (b lambda epsilon : ℝ) (I : Coord → ℝ) (p : Coord) (hp : p 1 = b) :
    directedM b lambda I p = 0 ∧ directedN b lambda epsilon I p = 0 := by
  simp [directedM, directedN, directedWeight_edge_zero b lambda I p hp]

end SmoothLocal.Weighted

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

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem intervalCutoff_contDiff (a b : ℝ) : ContDiff ℝ ∞ (intervalCutoff a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (b - a))

theorem intervalCutoff_range (a b x : ℝ) :
    0 ≤ intervalCutoff a b x ∧ intervalCutoff a b x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem intervalCutoff_one {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    intervalCutoff a b x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)

theorem threeEdgeCutoff_contDiff (l0 l1 r1 r0 a0 a1 : ℝ) :
    ContDiff ℝ ∞ (threeEdgeCutoff l0 l1 r1 r0 a0 a1) := by
  exact (((intervalCutoff_contDiff l0 l1).comp (contDiff_apply ℝ ℝ 0)).mul
    ((intervalCutoff_contDiff (-r0) (-r1)).comp (contDiff_apply ℝ ℝ 0).neg)).mul
      ((intervalCutoff_contDiff a0 a1).comp (contDiff_apply ℝ ℝ 1))

theorem threeEdgeCutoff_range (l0 l1 r1 r0 a0 a1 : ℝ) (p : Coord) :
    0 ≤ threeEdgeCutoff l0 l1 r1 r0 a0 a1 p ∧
      threeEdgeCutoff l0 l1 r1 r0 a0 a1 p ≤ 1 := by
  have hL := intervalCutoff_range l0 l1 (p 0)
  have hR := intervalCutoff_range (-r0) (-r1) (-p 0)
  have hS := intervalCutoff_range a0 a1 (p 1)
  constructor
  · exact mul_nonneg (mul_nonneg hL.1 hR.1) hS.1
  · have hLR : intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) ≤ 1 := by
      nlinarith
    change intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
      intervalCutoff a0 a1 (p 1) ≤ 1
    nlinarith [mul_nonneg hL.1 hR.1]

theorem threeEdgeCutoff_one {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (p : Coord)
    (hp : l1 ≤ p 0 ∧ p 0 ≤ r1 ∧ a1 ≤ p 1) :
    threeEdgeCutoff l0 l1 r1 r0 a0 a1 p = 1 := by
  rw [threeEdgeCutoff, intervalCutoff_one hL hp.1,
    intervalCutoff_one (neg_lt_neg hR) (neg_le_neg hp.2.1),
    intervalCutoff_one hS hp.2.2]
  norm_num

theorem capSpatialCutoff_contDiff (L R A : ℝ) :
    ContDiff ℝ ∞ (capSpatialCutoff L R A) := threeEdgeCutoff_contDiff _ _ _ _ _ _

theorem capSpatialCutoff_range (L R A : ℝ) (p : Coord) :
    0 ≤ capSpatialCutoff L R A p ∧ capSpatialCutoff L R A p ≤ 1 :=
  threeEdgeCutoff_range _ _ _ _ _ _ p

theorem capSpatialCutoff_one {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (p : Coord)
    (hp : L ≤ p 0 ∧ p 0 ≤ R ∧ A ≤ p 1) : capSpatialCutoff L R A p = 1 := by
  obtain ⟨hlo, hli, hlu, hlx⟩ := capEdges_bounds hL
  obtain ⟨hro, hri, hru, hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao, hai, hau, hax⟩ := capEdges_bounds hA
  apply threeEdgeCutoff_one hli (neg_lt_neg hri) hai p
  exact ⟨by linarith [hp.1], by linarith [hp.2.1], by linarith [hp.2.2]⟩

end SmoothLocal.Weighted

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

theorem coordinatePrimitive_segment_intervalIntegrable
    (hB : ContinuousOn B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b) :
    IntervalIntegrable (fun t => B (coordinatePoint t (p 1))) volume 0 (p 0) := by
  have hc : ContinuousOn (fun t => B (coordinatePoint t (p 1))) (Ioo (-R) R) :=
    hB.comp (by unfold coordinatePoint; fun_prop)
      (fun t ht => point_mem_rectangle ht hp.2)
  have hz : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
  have hseg : uIcc 0 (p 0) ⊆ Ioo (-R) R := by
    intro t ht
    exact ⟨lt_of_lt_of_le (lt_min hz.1 hp.1.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hz.2 hp.1.2)⟩
  exact (hc.mono hseg).intervalIntegrable

theorem coordinatePrimitive_abs_bound
    (hB : ContinuousOn B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b)
    {M : ℝ} (hbound : ∀ q ∈ coordinateRectangle R a b, |B q| ≤ M) :
    |coordinatePrimitive B p| ≤ R * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbound p hp)
  have hz : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
  have hseg : uIcc 0 (p 0) ⊆ Ioo (-R) R := by
    intro t ht
    exact ⟨lt_of_lt_of_le (lt_min hz.1 hp.1.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hz.2 hp.1.2)⟩
  have hi := coordinatePrimitive_segment_intervalIntegrable hB hR hp
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := p 0) (C := M)
    (f := fun t => B (coordinatePoint t (p 1)))
    (fun t ht => by
      rw [Real.norm_eq_abs]
      exact hbound _ (point_mem_rectangle (hseg (uIoc_subset_uIcc ht)) hp.2))
  calc
    _ ≤ M * |p 0| := by simpa only [coordinatePrimitive, Real.norm_eq_abs, sub_zero] using hb
    _ ≤ M * R := mul_le_mul_of_nonneg_left (abs_lt.mpr hp.1).le hM
    _ = R * M := mul_comm _ _

theorem coordinatePrimitive_partial_s_bound
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b)
    {M : ℝ} (hBs : ∀ q ∈ coordinateRectangle R a b, |coordPartial 1 B q| ≤ M) :
    |coordPartial 1 (coordinatePrimitive B) p| ≤ R * M := by
  rw [coordinatePrimitive_partial_s hB hR hp]
  exact coordinatePrimitive_abs_bound
    (partial_contDiffOn hB (coordinateRectangle_isOpen R a b) 1).continuousOn hR hp hBs

end SmoothLocal.Weighted

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
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def coordinateSubsetIntegral (S : Set Coord) (f : Coord → ℝ) : ℝ :=
  ∫ q in (fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' S, f (boxPoint q.1 q.2)

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

theorem coordinateSubset_preimage_mem (hSbox : S ⊆ closedRectangle tl tr sb st)
    {q : ℝ × ℝ} (hq : q ∈ (fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' S) :
    q ∈ Icc tl tr ×ˢ Icc sb st := by
  have hp := hSbox hq
  change q.1 ∈ Icc tl tr ∧ q.2 ∈ Icc sb st
  change (boxPoint q.1 q.2) 0 ∈ Icc tl tr ∧ (boxPoint q.1 q.2) 1 ∈ Icc sb st at hp
  have h0 : (boxPoint q.1 q.2) 0 = q.1 := by simp [boxPoint]
  have h1 : (boxPoint q.1 q.2) 1 = q.2 := by simp [boxPoint]
  rwa [h0, h1] at hp

theorem coordinateSubset_integrable
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hSbox : S ⊆ closedRectangle tl tr sb st) :
    IntegrableOn (fun q : ℝ × ℝ => F (boxPoint q.1 q.2))
      ((fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' S) :=
  (coordinateRectangle_closed_area_integrable hF).mono_set
    (fun _ hq => coordinateSubset_preimage_mem hSbox hq)

theorem coordinateSubsetIntegral_mono (hS : MeasurableSet S)
    (hSbox : S ⊆ closedRectangle tl tr sb st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hG : ContinuousOn G (closedRectangle tl tr sb st))
    (hle : ∀ p ∈ S, F p ≤ G p) :
    coordinateSubsetIntegral S F ≤ coordinateSubsetIntegral S G := by
  have hm : MeasurableSet ((fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' S) :=
    hS.preimage (by unfold boxPoint; fun_prop)
  apply setIntegral_mono_on (coordinateSubset_integrable hF hSbox)
    (coordinateSubset_integrable hG hSbox) hm
  intro q hq
  exact hle (boxPoint q.1 q.2) hq

theorem coordinateSubsetIntegral_le_rectangle
    (ht : tl ≤ tr) (hs : sb ≤ st) (hSbox : S ⊆ closedRectangle tl tr sb st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hn : ∀ p ∈ closedRectangle tl tr sb st, 0 ≤ F p) :
    coordinateSubsetIntegral S F ≤ rectangleIntegral tl tr sb st F := by
  rw [rectangleIntegral_eq_closed_area ht hs hF]
  have hnonneg : (0 : ℝ × ℝ → ℝ) ≤ᵐ[volume.restrict (Icc tl tr ×ˢ Icc sb st)]
      (fun q => F (boxPoint q.1 q.2)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with q hq
    exact hn (boxPoint q.1 q.2) (boxPoint_mem hq.1 hq.2)
  exact setIntegral_mono_set (coordinateRectangle_closed_area_integrable hF) hnonneg
    (Filter.Eventually.of_forall (fun _ hq => coordinateSubset_preimage_mem hSbox hq))

theorem coordinateSubsetIntegral_const_mul (S : Set Coord) (r : ℝ) (F : Coord → ℝ) :
    coordinateSubsetIntegral S (fun p => r * F p) = r * coordinateSubsetIntegral S F := by
  unfold coordinateSubsetIntegral
  exact integral_const_mul r _

theorem restricted_gradient_from_energy
    (ht : tl ≤ tr) (hs : sb ≤ st) (hS : MeasurableSet S)
    (hSbox : S ⊆ closedRectangle tl tr sb st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hG : ContinuousOn G (closedRectangle tl tr sb st))
    (hn : ∀ p ∈ closedRectangle tl tr sb st, 0 ≤ G p)
    {Q : ℝ} (hQ : 0 ≤ Q) (hFG : ∀ p ∈ S, F p ≤ Q * G p) :
    coordinateSubsetIntegral S F ≤ Q * rectangleIntegral tl tr sb st G := by
  calc
    _ ≤ coordinateSubsetIntegral S (fun p => Q * G p) :=
      coordinateSubsetIntegral_mono hS hSbox hF (continuousOn_const.mul hG) hFG
    _ = Q * coordinateSubsetIntegral S G := coordinateSubsetIntegral_const_mul _ _ _
    _ ≤ Q * rectangleIntegral tl tr sb st G :=
      mul_le_mul_of_nonneg_left (coordinateSubsetIntegral_le_rectangle ht hs hSbox hG hn) hQ

variable {U : Set Coord} {K G1 B C u f : Coord → ℝ}
  {l0 l1 r1 r0 a0 a1 b c c1 MK g0 M : ℝ}

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem directedQuadratic_edge_zero
    (A B C I u : Coord → ℝ) (edge lambda epsilon : ℝ) (p : Coord)
    (hA : DifferentiableAt ℝ A p) (hI : DifferentiableAt ℝ I p) (hedge : p 1 = edge) :
    multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p = 0 := by
  have hW := directedWeight_edge_zero edge lambda I p hedge
  have hWd (i : Fin 2) := directedWeight_partial_edge_zero edge lambda hI hedge i
  have hm := directedM_differentiableAt edge lambda hI
  have hn := directedN_differentiableAt edge lambda epsilon hI
  obtain ⟨hm0, hn0⟩ := directed_mn_edge_zero edge lambda epsilon I p hedge
  have hmd (i : Fin 2) : coordPartial i (directedM edge lambda I) p = 0 := by
    rw [directedM_partial, hWd i, neg_zero]
  have hnd (i : Fin 2) : coordPartial i (directedN edge lambda epsilon I) p = 0 := by
    rw [directedN_partial edge lambda epsilon hI i, hW, hWd i]
    ring
  have hAm (i : Fin 2) : coordPartial i (fun q => A q * directedM edge lambda I q) p = 0 := by
    rw [HessianCalculus.coordPartial_mul_at hA hm i, hm0, hmd i]
    ring
  have hAn (i : Fin 2) : coordPartial i (fun q => A q * directedN edge lambda epsilon I q) p = 0 := by
    rw [HessianCalculus.coordPartial_mul_at hA hn i, hn0, hnd i]
    ring
  simp only [multiplierQuadratic, multiplierT, multiplierS, multiplierJ,
    hmd, hnd, hAm, hAn, hm0, hn0]
  ring

end SmoothLocal.Weighted

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

theorem heightChartA_eq (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : Coord) :
    heightChartA g z Y p = heightChartG1 g z Y p * capPullback Y (gaussianCurvature g) p := by
  unfold heightChartA heightChartG1 capTransportA capPullback heightOriginalA
  ring

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

theorem heightChartA_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) :
    ContDiffOn ℝ ∞ (heightChartA g z Y) capChartDomain :=
  (capPullback_contDiffOn hY (heightOriginalA_contDiffOn hg hU hz hyy) hmap).mul
    ((capChartRho_contDiffOn hY hvar).pow 2)

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

theorem heightChartC_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hE : ∀ p ∈ U, 0 < heightEnergy g z p)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightChartC g z Y ell) capChartDomain := by
  have hA := heightChartA_contDiffOn hg hU hz hyy hY hvar hmap
  have hr := heightChartRemainder_contDiffOn hg hU hz hyy hE hY hvar hmap ell
  exact ((contDiffOn_const.mul (partial_contDiffOn hA capChartDomain_isOpen 1)).add (hA.mul hr)).congr
    (fun _ hp => heightChartC_factor hg hU hz hD hyy hE hY hvar hmap hp ell)

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
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem heightChartA_negative_of_curvature
    (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : Coord)
    {cG delta : ℝ} (hcG : 0 < cG) (hdelta : 0 < delta)
    (hG : cG ≤ heightChartG1 g z Y p)
    (hK : capPullback Y (gaussianCurvature g) p ≤ -delta) :
    heightChartA g z Y p ≤ -(cG * delta) := by
  rw [heightChartA_eq]
  have hGpos : 0 ≤ heightChartG1 g z Y p := (hcG.trans_le hG).le
  calc
    _ ≤ heightChartG1 g z Y p * (-delta) := mul_le_mul_of_nonneg_left hK hGpos
    _ ≤ cG * (-delta) := mul_le_mul_of_nonpos_right hG (by linarith)
    _ = _ := by ring

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
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow

theorem gaussianCurvature_coordinate_bound_one_closed
    {g : MetricField} {U : Set Coord} {G d : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|) :
    CoordinateBound (gaussianCurvature g) modelSquare 1 (curvatureFirstBound G d) := by
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun i j => (hg.1 i j).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  apply CoordinateBound.of_modelSquare_interior (gaussianCurvature_contDiffOn hg hU) hU hSU
  exact gaussianCurvature_coordinate_bound_one hgI isOpen_interior hG hd
    (fun i j => (hgB i j).restrict_domain interior_subset) (fun p hp => hdet p (interior_subset hp))

end SmoothLocal.Geometry

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem capFlowHeight_partial_bound_of_rho
    {q : Coord → ℝ} {Y : ℝ → ℝ → ℝ} {M : ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hmapS : MapsTo (capChart Y) capChartDomain modelSquare)
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    (hM : 0 ≤ M) (hrho : ∀ p ∈ capChartDomain, 1 / Real.exp (2 * M) ≤ capChartRho Y p)
    {p : Coord} (hp : p ∈ capChartDomain) (i : Fin 2) :
    |coordPartial i (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
  fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one]
  · rw [capFlowHeight_partial_time hY hode hp, abs_neg]
    exact (hsmall _ (hmapS hp)).trans ((by norm_num : (1 : ℝ) / 100 ≤ 1).trans
      (flowCoordinateBound_dominates hM).2.1)
  · have hpos := capFlowHeight_partial_initial_pos hY hvar hp
    rw [abs_of_pos hpos]
    have hl : 1 / Real.exp (2 * M) ≤ 1 / coordPartial 1 (capFlowHeight Y) p := hrho p hp
    have hupper : coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2 * M) := by
      simpa only [one_mul] using (div_le_div_iff₀ (Real.exp_pos _) hpos).mp hl
    exact hupper.trans (flowCoordinateBound_dominates hM).2.2.1

theorem capPullback_bound_one_from_partials
    {u : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {A F : ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U)
    (hmapS : MapsTo (capChart Y) capChartDomain modelSquare)
    (hA : 0 ≤ A) (hF : 0 ≤ F) (huB : CoordinateBound u modelSquare 1 A)
    (hFB : ∀ i : Fin 2, ∀ p ∈ capChartDomain, |coordPartial i (capFlowHeight Y) p| ≤ F) :
    CoordinateBound (capPullback Y u) capChartDomain 1 (A * (1 + F)) := by
  intro ds hds p hp
  cases ds with
  | nil => exact (huB [] (by norm_num) _ (hmapS hp)).trans (by nlinarith [mul_nonneg hA hF])
  | cons i ds =>
    cases ds with
    | nil =>
      change |coordPartial i (capPullback Y u) p| ≤ A * (1 + F)
      rw [capPullback_partial hY hp ((hu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp)) i]
      have hdu (j : Fin 2) : |coordPartial j u (capChart Y p)| ≤ A := huB [j] (by norm_num) _ (hmapS hp)
      have h0 : |if i = 0 then coordPartial 0 u (capChart Y p) else 0| ≤ A := by
        split_ifs
        · exact hdu 0
        · simpa only [abs_zero] using hA
      have h1 : |coordPartial 1 u (capChart Y p) * coordPartial i (capFlowHeight Y) p| ≤ A * F := by
        rw [abs_mul]
        exact mul_le_mul (hdu 1) (hFB i p hp) (abs_nonneg _) hA
      exact ((abs_add_le _ _).trans (add_le_add h0 h1)).trans (le_of_eq (by ring))
    | cons j ds => simp only [List.length_cons] at hds; omega

theorem heightChartA_bound_one
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hmapS : MapsTo (capChart Y) capChartDomain modelSquare)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ) / 100)
    (hrho : ∀ p ∈ capChartDomain,
      1 / Real.exp (2 * heightQuotientJetBound G Z d c) ≤ capChartRho Y p)
    (hG1s : ContDiffOn ℝ ∞ (heightChartG1 g z Y) capChartDomain)
    (hG1B : CoordinateBound (heightChartG1 g z Y) capChartDomain 1 (heightG1JetBound G Z d c)) :
    CoordinateBound (heightChartA g z Y) capChartDomain 1 (heightAJetBound G Z d c) := by
  have hM := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hM
  have hK := curvatureFirstBound_nonneg hG hd
  have hG1 := heightG1JetBound_nonneg hG hZ hd hc
  have hmapU : MapsTo (capChart Y) capChartDomain U := fun p hp => hSU (hmapS hp)
  have hKs := gaussianCurvature_contDiffOn hg hU
  have hKB := capPullback_bound_one_from_partials hY hKs hU hmapU hmapS hK hF
    (gaussianCurvature_coordinate_bound_one_closed hg hU hSU hG hd hgB hdet)
    (fun i p hp => capFlowHeight_partial_bound_of_rho hY hvar hode hmapS hsmall hM hrho hp i)
  have hb := CoordinateBound.mul_through_one hG1s (capPullback_contDiffOn hY hKs hmapU)
    capChartDomain_isOpen hG1 (mul_nonneg hK (by positivity)) hG1B hKB
  exact CoordinateBound.congr_on capChartDomain_isOpen hb (fun p _ => heightChartA_eq g z Y p)

theorem heightChartB_primitive_bounds
    {g : MetricField} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ} {MB : ℝ} (ell : ℕ)
    (hB : ContDiffOn ℝ ∞ (heightChartB g z Y ell) capChartDomain)
    (hBB : CoordinateBound (heightChartB g z Y ell) capChartDomain 1 MB)
    {p : Coord} (hp : p ∈ capChartDomain) :
    |coordinatePrimitive (heightChartB g z Y ell) p| ≤ 2 * MB ∧
    |coordPartial 1 (coordinatePrimitive (heightChartB g z Y ell)) p| ≤ 2 * MB := by
  exact ⟨coordinatePrimitive_abs_bound hB.continuousOn (by norm_num : (0 : ℝ) < 2) hp
      (fun q hq => hBB [] (by norm_num) q hq),
    coordinatePrimitive_partial_s_bound hB (by norm_num : (0 : ℝ) < 2) hp
      (fun q hq => hBB [1] (by norm_num) q hq)⟩

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
open SmoothLocal.Geometry SmoothLocal.Flow

theorem capInteriorWeightFloor_pos {top b lambda MI : ℝ} (htop : top < b) :
    0 < capInteriorWeightFloor top b lambda MI :=
  mul_pos (pow_pos (sub_pos.mpr htop) _) (Real.exp_pos _)

theorem directedWeight_interior_lower {I : Coord → ℝ} {p : Coord} {top b lambda MI : ℝ}
    (htop : top < b) (hlambda : 0 ≤ lambda) (hp : p 1 ≤ top) (hI : |I p| ≤ MI) :
    capInteriorWeightFloor top b lambda MI ≤ directedWeight b lambda I p := by
  have hdist : b-top ≤ edgeDistance b p := by unfold edgeDistance; linarith
  have hpow := pow_le_pow_left₀ (sub_pos.mpr htop).le hdist 8
  have hphase : -lambda*top-MI ≤ weightPhase lambda I p := by
    have hm := mul_le_mul_of_nonneg_left hp hlambda
    unfold weightPhase
    linarith [(abs_le.mp hI).1]
  exact mul_le_mul hpow (Real.exp_le_exp.mpr hphase) (Real.exp_pos _).le
    (pow_nonneg ((sub_pos.mpr htop).le.trans hdist) _)

theorem closedRectangle_measurable (tl tr sb st : ℝ) : MeasurableSet (closedRectangle tl tr sb st) := by
  have h0 : IsClosed ((fun p : Coord => p 0) ⁻¹' Icc tl tr) := isClosed_Icc.preimage (continuous_apply 0)
  have h1 : IsClosed ((fun p : Coord => p 1) ⁻¹' Icc sb st) := isClosed_Icc.preimage (continuous_apply 1)
  exact (h0.inter h1).measurableSet

theorem coordinateSubsetIntegral_closedRectangle (tl tr sb st : ℝ) (F : Coord → ℝ)
    (ht : tl ≤ tr) (hs : sb ≤ st) (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    coordinateSubsetIntegral (closedRectangle tl tr sb st) F = rectangleIntegral tl tr sb st F := by
  rw [rectangleIntegral_eq_closed_area ht hs hF]
  have hpre : (fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' closedRectangle tl tr sb st =
      Icc tl tr ×ˢ Icc sb st := by
    ext q
    simp [closedRectangle,boxPoint,Prod.le_def,and_left_comm,and_assoc]
  unfold coordinateSubsetIntegral
  rw [hpre]

theorem capInterior_gradient_le_directed_energy
    {L R bottom top b lambda MI : ℝ} {I u : Coord → ℝ}
    (hL : -2 < L) (hR : R < 2) (hbottom : -2 < bottom)
    (hLR : L ≤ R) (hbt : bottom ≤ top) (htop : top < b) (hb : b ≤ 0)
    (hlambda : 0 ≤ lambda) (hI : ContDiffOn ℝ ∞ I capChartDomain)
    (hu : ContDiffOn ℝ ∞ u capChartDomain)
    (hIv : ∀ p ∈ closedRectangle L R bottom top, |I p| ≤ MI) :
    rectangleIntegral L R bottom top (fun p => (coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤
      (1/capInteriorWeightFloor top b lambda MI)*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
          (directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda) := by
  let F := fun p => (coordPartial 0 u p)^2+(coordPartial 1 u p)^2
  let E := directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda
  let S := closedRectangle L R bottom top
  let T := closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
  have hwpos := capInteriorWeightFloor_pos (lambda := lambda) (MI := MI) htop
  obtain ⟨htlo,htwidth,htone,hrone,hrwidth,htrhi,hsblo,hswidth,hsone,hlt,hrt⟩ :=
    capOuterRectangle_edges hL hR hbottom
  have ht : capOuterLeft L ≤ capOuterRight R := by linarith
  have hs : capOuterBottom bottom ≤ b := by linarith
  have hT : T ⊆ capChartDomain := capOuterRectangle_subset_domain hL hR hbottom (by linarith)
  have hST : S ⊆ T := by
    intro p hp
    exact ⟨⟨hlt.le.trans hp.1.1,hp.1.2.trans hrt.le⟩,
      ⟨(by linarith [hp.2.1]),hp.2.2.trans htop.le⟩⟩
  have hgrad := ((partial_contDiffOn hu capChartDomain_isOpen 0).pow 2).add
    ((partial_contDiffOn hu capChartDomain_isOpen 1).pow 2)
  have hFc : ContinuousOn F T := hgrad.continuousOn.mono hT
  have hEc : ContinuousOn E T :=
    ((((capSpatialCutoff_contDiff L R bottom).contDiffOn.mul
      (directedWeight_contDiffOn b lambda hI)).mul hgrad).continuousOn.mono hT)
  have hEn (p : Coord) (hp : p ∈ T) : 0 ≤ E p := by
    have hchi := (capSpatialCutoff_range L R bottom p).1
    have hd : 0 ≤ edgeDistance b p := sub_nonneg.mpr hp.2.2
    unfold E directedGradientEnergy directedWeight
    positivity
  have hpoint (p : Coord) (hp : p ∈ S) : F p ≤ (1/capInteriorWeightFloor top b lambda MI)*E p := by
    have hW := directedWeight_interior_lower htop hlambda hp.2.2 (hIv p hp)
    have hchi := capSpatialCutoff_one hL hR hbottom p ⟨hp.1.1,hp.1.2,hp.2.1⟩
    have hgrad0 : 0 ≤ F p := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hh := mul_le_mul_of_nonneg_right hW hgrad0
    have hscaled : capInteriorWeightFloor top b lambda MI*F p ≤ E p := by
      simpa only [E,directedGradientEnergy,hchi,one_mul] using hh
    have hdiv : F p ≤ E p/capInteriorWeightFloor top b lambda MI :=
      (le_div_iff₀ hwpos).mpr (by simpa only [mul_comm] using hscaled)
    convert hdiv using 1 <;> try with_reducible_and_instances rfl
    ring
  have hcomp := restricted_gradient_from_energy ht hs (closedRectangle_measurable _ _ _ _)
    hST hFc hEc hEn (show 0 ≤ 1/capInteriorWeightFloor top b lambda MI by positivity) hpoint
  rw [coordinateSubsetIntegral_closedRectangle L R bottom top F hLR hbt (hFc.mono hST)] at hcomp
  exact hcomp

end SmoothLocal.Weighted

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

theorem heightCapCurvatureBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightCapCurvatureBound G Z d c := by
  have hK := curvatureFirstBound_nonneg hG hd
  have hF := flowCoordinateBound_nonneg (heightQuotientJetBound_nonneg hG hZ hd hc)
  unfold heightCapCurvatureBound
  positivity

theorem heightCapCoefficientBound_dominates {G Z d c e0 : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0) (ell : ℕ) :
    0 ≤ heightCapCoefficientBound G Z d c e0 ell ∧
    heightAJetBound G Z d c ≤ heightCapCoefficientBound G Z d c e0 ell ∧
    2*heightBJetBound G Z d c ell ≤ heightCapCoefficientBound G Z d c e0 ell ∧
    heightBJetBound G Z d c ell ≤ heightCapCoefficientBound G Z d c e0 ell ∧
    heightCapCValueBound G Z d c e0 ell ≤ heightCapCoefficientBound G Z d c e0 ell := by
  have hA := heightAJetBound_nonneg hG hZ hd hc
  have hB := heightBJetBound_nonneg hG hZ hd hc ell
  have hr := heightRemainderBound_nonneg hG hZ hd hc he0 ell
  have hC : 0 ≤ heightCapCValueBound G Z d c e0 ell := by
    unfold heightCapCValueBound
    positivity
  unfold heightCapCoefficientBound
  constructor
  · positivity
  constructor
  · linarith only [hB,hC]
  constructor
  · linarith only [hA,hC]
  constructor
  · linarith only [hA,hB,hC]
  · linarith only [hA,hB]

theorem heightChartC_value_bound
    {g : MetricField} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ} {G Z d c e0 : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0) (ell : ℕ)
    (hAB : CoordinateBound (heightChartA g z Y) capChartDomain 1 (heightAJetBound G Z d c))
    (hrB : ∀ p ∈ capChartDomain,
      |heightChartRemainder g z Y ell p| ≤ heightRemainderBound G Z d c e0 ell ∧
      heightChartC g z Y ell p = ((ell : ℝ)+1)*coordPartial 1 (heightChartA g z Y) p +
        heightChartA g z Y p*heightChartRemainder g z Y ell p)
    {p : Coord} (hp : p ∈ capChartDomain) :
    |heightChartC g z Y ell p| ≤ heightCapCValueBound G Z d c e0 ell := by
  have hel : 0 ≤ (ell : ℝ)+1 := by positivity
  have hfirst := mul_le_mul_of_nonneg_left (hAB [1] (by norm_num) p hp) hel
  have hsecond :=
    (mul_le_mul_of_nonneg_left (hrB p hp).1 (abs_nonneg (heightChartA g z Y p))).trans
      (mul_le_mul_of_nonneg_right (hAB [] (by norm_num) p hp)
        (heightRemainderBound_nonneg hG hZ hd hc he0 ell))
  rw [(hrB p hp).2]
  calc
    _ ≤ |((ell : ℝ)+1)*coordPartial 1 (heightChartA g z Y) p| +
        |heightChartA g z Y p*heightChartRemainder g z Y ell p| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul,abs_of_nonneg hel,abs_mul]
      exact add_le_add hfirst hsecond

theorem heightChartB_primitive_first_bounds
    {g : MetricField} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ} {MB : ℝ} (ell : ℕ)
    (hMB : 0 ≤ MB) (hB : ContDiffOn ℝ ∞ (heightChartB g z Y ell) capChartDomain)
    (hBB : CoordinateBound (heightChartB g z Y ell) capChartDomain 1 MB)
    {p : Coord} (hp : p ∈ capChartDomain) :
    |coordinatePrimitive (heightChartB g z Y ell) p| ≤ 2*MB ∧
      ∀ i : Fin 2, |coordPartial i (coordinatePrimitive (heightChartB g z Y ell)) p| ≤ 2*MB := by
  obtain ⟨hIv,hIs⟩ := heightChartB_primitive_bounds ell hB hBB hp
  refine ⟨hIv,?_⟩
  intro i
  fin_cases i
  · simp only [Fin.mk_zero]
    rw [coordinatePrimitive_partial_t hB (by norm_num : (0 : ℝ) < 2) hp]
    exact (hBB [] (by norm_num) p hp).trans (by linarith only [hMB])
  · simpa only [Fin.mk_one] using hIs

theorem heightCurvaturePullback_bound_one
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hmapS : MapsTo (capChart Y) capChartDomain modelSquare)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ)/100)
    (hrho : ∀ p ∈ capChartDomain, 1/Real.exp (2*heightQuotientJetBound G Z d c) ≤ capChartRho Y p) :
    CoordinateBound (capPullback Y (gaussianCurvature g)) capChartDomain 1 (heightCapCurvatureBound G Z d c) := by
  have hM := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hM
  have hK := curvatureFirstBound_nonneg hG hd
  exact capPullback_bound_one_from_partials hY (gaussianCurvature_contDiffOn hg hU) hU
    (fun p hp => hSU (hmapS hp)) hmapS hK hF
    (gaussianCurvature_coordinate_bound_one_closed hg hU hSU hG hd hgB hdet)
    (fun i p hp => capFlowHeight_partial_bound_of_rho hY hvar hode hmapS hsmall hM hrho hp i)

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
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

theorem heightDirectedNumbers_spec {G Z d c e0 kappa : ℝ}
    (h : HeightNumericData G Z d c e0 kappa) (ell : ℕ) :
    HeightDirectedBudgets G Z d c e0 kappa ell (heightDirectedNumbers G Z d c e0 kappa ell) := by
  rw [heightDirectedNumbers,dite_eq_left h]
  exact Classical.choose_spec (exists_heightDirectedBudgets h ell)

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
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

theorem exists_patch_uniform_numeric_directed_flow
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0 + eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => (g0 + eta) p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0 + eta) p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian (g0 + eta) z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0 + eta) z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0 + eta) z p| ≤ (1 : ℝ) / 100)
    (hD : ∀ p ∈ modelSquare,
      (covHessian (g0 + eta) z p).det = gaussianCurvature (g0 + eta) p * heightEnergy (g0 + eta) z p)
    (hk : 0 < kappa)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (ell : ℕ) :
    let epsilon := heightDirectedEpsilon G Z d c e0 kappa ell
    let lambda := heightDirectedLambda G Z d c e0 kappa ell
    let c1 := heightDirectedSlope G Z d c e0 kappa ell
    let c2 := heightDirectedCoercivity G Z d c e0 kappa ell
    ∃ Y : ℝ → ℝ → ℝ,
      0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧ 0 < c2 ∧
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient (g0 + eta) z (coordinatePoint t (Y s t)))
          (Icc (-2 : ℝ) 2) t) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) ∧
      ContDiffOn ℝ ∞ (heightChartA (g0 + eta) z Y) capChartDomain ∧
      ContDiffOn ℝ ∞ (heightChartB (g0 + eta) z Y ell) capChartDomain ∧
      ContDiffOn ℝ ∞ (heightChartC (g0 + eta) z Y ell) capChartDomain ∧
      ContDiffOn ℝ ∞ (coordinatePrimitive (heightChartB (g0 + eta) z Y ell)) capChartDomain ∧
      ContDiffOn ℝ ∞ (capPullback Y (gaussianCurvature (g0 + eta))) capChartDomain ∧
      ContDiffOn ℝ ∞ (heightChartG1 (g0 + eta) z Y) capChartDomain ∧
      (∀ p ∈ capChartDomain,
        heightG1Lower G Z d c e0 ≤ heightChartG1 (g0 + eta) z Y p ∧
        |coordinatePrimitive (heightChartB (g0 + eta) z Y ell) p| ≤ 2*heightBJetBound G Z d c ell ∧
        (∀ i : Fin 2, |coordPartial i (coordinatePrimitive (heightChartB (g0 + eta) z Y ell)) p| ≤
          heightCapCoefficientBound G Z d c e0 ell) ∧
        (∀ i : Fin 2, |coordPartial i (capPullback Y (gaussianCurvature (g0 + eta))) p| ≤
          heightCapCurvatureBound G Z d c) ∧
        |heightChartA (g0 + eta) z Y p| ≤ heightCapCoefficientBound G Z d c e0 ell ∧
        (∀ i : Fin 2, |coordPartial i (heightChartA (g0 + eta) z Y) p| ≤
          heightCapCoefficientBound G Z d c e0 ell) ∧
        |heightChartB (g0 + eta) z Y ell p| ≤ heightCapCoefficientBound G Z d c e0 ell ∧
        |heightChartC (g0 + eta) z Y ell p| ≤ heightCapCoefficientBound G Z d c e0 ell) ∧
      ∀ edge : ℝ, edge ≤ 0 → ∀ p ∈ capChartDomain, p 1 < edge →
        capPullback Y (gaussianCurvature (g0 + eta)) p ≤ c1 * (edge - p 1) →
        ∀ x y : ℝ,
          let A := heightChartA (g0 + eta) z Y
          let B := heightChartB (g0 + eta) z Y ell
          let C := heightChartC (g0 + eta) z Y ell
          let I := coordinatePrimitive B
          c2 * directedWeight edge lambda I p * (x^2 + y^2) ≤
            multiplierT B (directedM edge lambda I) (directedN edge lambda epsilon I) p * x^2 +
            multiplierS A C (directedM edge lambda I) (directedN edge lambda epsilon I) p * y^2 +
            multiplierJ A B C (directedM edge lambda I) (directedN edge lambda epsilon I) p * x * y := by
  let M := heightQuotientJetBound G Z d c
  let cG := heightG1Lower G Z d c e0
  let rhoMax := 1 / Real.exp (-2 * M)
  let MG := heightG1JetBound G Z d c
  let MB := heightBJetBound G Z d c ell
  let Mr := heightRemainderBound G Z d c e0 ell
  let MA := heightAJetBound G Z d c
  have hcG : 0 < cG := heightG1Lower_pos hG hZ hd he0
  have hrhoMax : 0 < rhoMax := by dsimp [rhoMax]; positivity
  have hMG : 0 ≤ MG := heightG1JetBound_nonneg hG hZ hd hc
  have hMB : 0 ≤ MB := heightBJetBound_nonneg hG hZ hd hc ell
  have hMr : 0 ≤ Mr := heightRemainderBound_nonneg hG hZ hd hc he0 ell
  have hMA : 0 ≤ MA := heightAJetBound_nonneg hG hZ hd hc
  let epsilon := heightDirectedEpsilon G Z d c e0 kappa ell
  let lambda := heightDirectedLambda G Z d c e0 kappa ell
  let c1 := heightDirectedSlope G Z d c e0 kappa ell
  obtain ⟨heps, heps1, hlambda, hc1, hqbudget, hTbudget, hEbudget,
      hcross, hloss, hfarbudget, hnearstrip, hstripbudget⟩ :=
    heightDirectedNumbers_spec ⟨hG,hZ,hd,hc,he0,hk⟩ ell
  let margin := modelCoercivityMargin cG kappa rhoMax epsilon ell
  let delta := modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell
  let c2 := min (lambda / 8) (margin / 4)
  have hmargin : 0 < margin := modelCoercivityMargin_pos ell hcG hk hrhoMax heps
  have hdelta : 0 < delta := modelPrincipalRadius_pos ell hcG hk hrhoMax heps (by norm_num) hMG
  have hc2 : 0 < c2 := by dsimp [c2]; positivity
  obtain ⟨Y, hchart, hYclosed, hYs, hvar, hstart, hode, hconf, hdisp50, hdisp,
      hrho, hG1s, hG1B, hGfloor, hall⟩ :=
    exists_height_flow_uniform_coefficients hg hU hSU hz hG hZ hd hc he0 hgB hzB hdet hyy hEfloor hsmall hD
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp p hp)
  have hmapS : MapsTo (capChart Y) capChartDomain modelSquare :=
    fun p hp => modelOpenSquare_subset (hmapO hp)
  have hAB := heightChartA_bound_one hg hU hSU hG hZ hd hc hgB hdet hYs hvar hode hmapS hsmall
    (fun p hp => (hrho p hp).2.1) hG1s hG1B
  obtain ⟨hBs, hBB, hrs, hrB⟩ := hall ell
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn (g0 + eta) modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU, fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hyyn := LowQuotient.denominator_ne_zero hc hyy
  have hyyO := fun p (hp : p ∈ modelOpenSquare) => hyyn p (modelOpenSquare_subset hp)
  have hEO := fun p (hp : p ∈ modelOpenSquare) => he0.trans_le (hEfloor p (modelOpenSquare_subset hp))
  have hDO := fun p (hp : p ∈ modelOpenSquare) => hD p (modelOpenSquare_subset hp)
  have hbackgroundO := fun p (hp : p ∈ modelOpenSquare) => hbackground p (hOU hp)
  have hAs := heightChartA_contDiffOn hgO modelOpenSquare_isOpen hzO hyyO hYs hvar hmapO
  have hKB := heightCurvaturePullback_bound_one hg hU hSU hG hZ hd hc hgB hdet
    hYs hvar hode hmapS hsmall (fun p hp => (hrho p hp).2.1)
  obtain ⟨hMF,hMFA,hMFI,hMFB,hMFC⟩ := heightCapCoefficientBound_dominates hG hZ hd hc he0 ell
  have hfixed (p : Coord) (hp : p ∈ capChartDomain) :
      heightG1Lower G Z d c e0 ≤ heightChartG1 (g0 + eta) z Y p ∧
      |coordinatePrimitive (heightChartB (g0 + eta) z Y ell) p| ≤ 2*heightBJetBound G Z d c ell ∧
      (∀ i : Fin 2, |coordPartial i (coordinatePrimitive (heightChartB (g0 + eta) z Y ell)) p| ≤
        heightCapCoefficientBound G Z d c e0 ell) ∧
      (∀ i : Fin 2, |coordPartial i (capPullback Y (gaussianCurvature (g0 + eta))) p| ≤
        heightCapCurvatureBound G Z d c) ∧
      |heightChartA (g0 + eta) z Y p| ≤ heightCapCoefficientBound G Z d c e0 ell ∧
      (∀ i : Fin 2, |coordPartial i (heightChartA (g0 + eta) z Y) p| ≤
        heightCapCoefficientBound G Z d c e0 ell) ∧
      |heightChartB (g0 + eta) z Y ell p| ≤ heightCapCoefficientBound G Z d c e0 ell ∧
      |heightChartC (g0 + eta) z Y ell p| ≤ heightCapCoefficientBound G Z d c e0 ell := by
    obtain ⟨hIv,hIi⟩ := heightChartB_primitive_first_bounds ell hMB hBs hBB hp
    exact ⟨hGfloor p hp,hIv,fun i => (hIi i).trans hMFI,
      fun i => hKB [i] (by norm_num) p hp,
      (hAB [] (by norm_num) p hp).trans hMFA,
      fun i => (hAB [i] (by norm_num) p hp).trans hMFA,
      (hBB [] (by norm_num) p hp).trans hMFB,
      (heightChartC_value_bound hG hZ hd hc he0 ell hAB hrB hp).trans hMFC⟩
  refine ⟨Y, heps, heps1, hlambda, hc1, hc2, hchart, hYs, hvar, hstart, hode, hdisp,
    hAs, hBs, heightChartC_contDiffOn hgO modelOpenSquare_isOpen hzO hDO hyyO hEO hYs hvar hmapO ell,
    coordinatePrimitive_contDiffOn hBs,
    capPullback_contDiffOn hYs (gaussianCurvature_contDiffOn hg hU) (fun p hp => hSU (hmapS hp)),
    hG1s,hfixed, ?_⟩
  intro edge hedge0 p hp hedge hKstrip x y
  have hs : p 1 ≤ 0 := (le_of_lt hedge).trans hedge0
  have hdist : edge - p 1 ≤ 2 := by linarith [hp.2.1]
  have hI := (heightChartB_primitive_bounds ell hBs hBB hp).2
  have hBpoint : |heightChartB (g0 + eta) z Y ell p| ≤ MB := hBB [] (by norm_num) p hp
  have hrpoint : |heightChartRemainder (g0 + eta) z Y ell p| ≤ Mr := (hrB p hp).1
  have hApoint : |heightChartA (g0 + eta) z Y p| ≤ MA := hAB [] (by norm_num) p hp
  have hAspoint : |coordPartial 1 (heightChartA (g0 + eta) z Y) p| ≤ MA := hAB [1] (by norm_num) p hp
  have hAtpoint : |coordPartial 0 (heightChartA (g0 + eta) z Y) p| ≤ MA := hAB [0] (by norm_num) p hp
  have hGspoint : |coordPartial 1 (heightChartG1 (g0 + eta) z Y) p| ≤ MG := hG1B [1] (by norm_num) p hp
  have hGtpoint : |coordPartial 0 (heightChartG1 (g0 + eta) z Y) p| ≤ MG := hG1B [0] (by norm_num) p hp
  have hGmax : heightChartG1 (g0 + eta) z Y p ≤ MG := (le_abs_self _).trans (hG1B [] (by norm_num) p hp)
  by_cases hnear : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤ delta
  · exact patch_actual_directed_near_coercivity hgO modelOpenSquare_isOpen hzO hDO hyyO hEO
      hYs hode hvar hdisp50 hsmall hmapO hbackgroundO hsupport hcentral hp hs ell
      cG rhoMax epsilon MG (2 * MB) MB Mr MA MA MG c1 2 edge lambda hk hcG (hGfloor p hp)
      (hrho p hp).2.2 heps heps1 hqbudget hGspoint hGtpoint hnear hedge hlambda hI hBpoint hrpoint
      hApoint hAspoint hTbudget hEbudget hcross hloss hGmax hc1.le hdist hKstrip hstripbudget x y
  · have hKupper : capPullback Y (gaussianCurvature (g0 + eta)) p ≤ delta :=
      hKstrip.trans ((mul_le_mul_of_nonneg_left hdist hc1.le).trans hnearstrip)
    have hKnegative : capPullback Y (gaussianCurvature (g0 + eta)) p ≤ -delta := by
      by_contra hneg
      exact hnear (abs_le.mpr ⟨(lt_of_not_ge hneg).le, hKupper⟩)
    have hAfar := heightChartA_negative_of_curvature (g0 + eta) z Y p hcG hdelta (hGfloor p hp) hKnegative
    have hloss' :
        (4 * (2 * ((ell : ℝ) * MA + MA * Mr + MA * (2 * MB) + 1))^2 * epsilon^2) / lambda ≤
          (margin / 2) / 4 := by
      calc
        _ ≤ margin / 8 := hloss
        _ = _ := by ring
    have hh := primitive_directed_farnegative_coercivity hBs (by norm_num : (0 : ℝ) < 2) hp
      (heightChartA (g0 + eta) z Y) (heightChartC (g0 + eta) z Y ell)
      (heightChartRemainder (g0 + eta) z Y ell)
      ((hAs.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp))
      edge lambda epsilon ell hedge hlambda heps.le heps1 (hrB p hp).2
      (2 * MB) MB Mr MA MA MA (margin / 2) (cG * delta) (by positivity)
      hI hBpoint hrpoint hApoint hAspoint hTbudget hEbudget hcross hloss' hAtpoint
      (mul_pos hcG hdelta) hAfar hfarbudget x y
    have hhalf : (margin / 2) / 2 = margin / 4 := by ring
    rw [hhalf] at hh
    exact hh

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

theorem exists_uniform_original_data_actual_high_cap_estimate
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => (g0+eta) p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian (g0+eta) z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0+eta) z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0+eta) z p| ≤ (1 : ℝ)/100)
    (hD : ∀ p ∈ modelSquare,
      (covHessian (g0+eta) z p).det = gaussianCurvature (g0+eta) p*heightEnergy (g0+eta) z p)
    (hk : 0 < kappa)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) (m : ℕ) :
    let epsilon := heightDirectedEpsilon G Z d c e0 kappa (m+3)
    let lambda := heightDirectedLambda G Z d c e0 kappa (m+3)
    let c1 := heightDirectedSlope G Z d c e0 kappa (m+3)
    let c2 := heightDirectedCoercivity G Z d c e0 kappa (m+3)
    ∃ Y : ℝ → ℝ → ℝ,
      0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧ 0 < c2 ∧
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient (g0+eta) z (coordinatePoint t (Y s t)))
          (Icc (-2 : ℝ) 2) t) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50) ∧
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
            (capPullback Y (verticalJet z (m+3))) (capPullback Y (actualHighRemainder (g0+eta) z m)) := by
  let epsilon := heightDirectedEpsilon G Z d c e0 kappa (m+3)
  let lambda := heightDirectedLambda G Z d c e0 kappa (m+3)
  let c1 := heightDirectedSlope G Z d c e0 kappa (m+3)
  let c2 := heightDirectedCoercivity G Z d c e0 kappa (m+3)
  obtain ⟨Y,heps,heps1,hlambda,hc1,hc2,hchart,hYs,hvar,hstart,hode,hdisp,
      hAs,hBs,hCs,hIs,hKs,hG1s,hfixed,hcoercive⟩ :=
    exists_patch_uniform_numeric_directed_flow hg hU hSU hz hG hZ hd hc he0 hgB hzB hdet hyy hEfloor
      hsmall hD hk hbackground hsupport hcentral (m+3)
  let g := g0+eta
  let u := capPullback Y (verticalJet z (m+3))
  let f := capPullback Y (actualHighRemainder g z m)
  let G1 := heightChartG1 g z Y
  let K := capPullback Y (gaussianCurvature g)
  let A := heightChartA g z Y
  let B := heightChartB g z Y (m+3)
  let C := heightChartC g z Y (m+3)
  let I := coordinatePrimitive B
  let M := heightCapCoefficientBound G Z d c e0 (m+3)
  let MK := heightCapCurvatureBound G Z d c
  let MI := 2*heightBJetBound G Z d c (m+3)
  let glow := heightG1Lower G Z d c e0
  have hM : 0 ≤ M := (heightCapCoefficientBound_dominates hG hZ hd hc he0 (m+3)).1
  have hMK : 0 ≤ MK := heightCapCurvatureBound_nonneg hG hZ hd hc
  have hglow : 0 < glow := heightG1Lower_pos hG hZ hd he0
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp p hp)
  have hyyO : ∀ p ∈ modelOpenSquare, covHessian g z p 1 1 ≠ 0 :=
    fun p hp => LowQuotient.denominator_ne_zero hc hyy p (modelOpenSquare_subset hp)
  have hu : ContDiffOn ℝ ∞ u capChartDomain := capPullback_contDiffOn hYs
    (verticalJet_contDiffOn modelOpenSquare_isOpen hzO (m+3)) hmapO
  have hPDE (p : Coord) (hp : p ∈ capChartDomain) : multiplierOperator A B C u p = f p :=
    actual_flow_high_equation hgO modelOpenSquare_isOpen hzO
      (fun p hp => hD p (modelOpenSquare_subset hp)) hyyO hYs hode hvar hmapO m hp
  have hAeq : A = (fun q => G1 q*K q) := by
    funext q
    exact heightChartA_eq g z Y q
  have hPDERaw : ∀ p ∈ capChartDomain, multiplierOperator (fun q => G1 q*K q) B C u p = f p := by
    intro p hp
    rw [←hAeq]
    exact hPDE p hp
  refine ⟨Y,heps,heps1,hlambda,hc1,hc2,hchart,hstart,hode,hdisp,hPDE,?_⟩
  intro L R bottom top b hL hR hbottom hLR hbt htop hb
  let T := closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
  let S := closedRectangle L R bottom top
  let D := capDistanceBound bottom b
  let COverlap := capOverlapEnergyCost L R bottom b kappa c1 c2 glow M lambda MI
  let HElliptic := capEllipticRatioBudget L R bottom b kappa c1 glow MK M
  let RHS := (((5/(2*c2))*(D^8*Real.exp (lambda*2+MI))+COverlap*D^6)*
      rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (f p)^2)) +
    ((COverlap*(D^6+HElliptic))*
      rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (u p)^2))
  have hT : T ⊆ capChartDomain := capOuterRectangle_subset_domain hL hR hbottom (by linarith)
  have hS : S ⊆ capChartDomain := by
    intro p hp
    exact ⟨⟨hL.trans_le hp.1.1,hp.1.2.trans_lt hR⟩,
      ⟨hbottom.trans_le hp.2.1,by linarith [hp.2.2]⟩⟩
  have hcoerceClosed (p : Coord) (hp : p ∈ T) (hK : K p ≤ c1*edgeDistance b p) :
      c2*directedWeight b lambda I p*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤
        multiplierQuadratic (fun q => G1 q*K q) B C (directedM b lambda I) (directedN b lambda epsilon I) u p := by
    rw [←hAeq]
    by_cases hedge : p 1 < b
    · have hh := hcoercive b hb p (hT hp) hedge hK (coordPartial 0 u p) (coordPartial 1 u p)
      unfold multiplierQuadratic
      convert hh using 1 <;> try with_reducible_and_instances rfl
    · have heq : p 1 = b := le_antisymm hp.2.2 (le_of_not_gt hedge)
      rw [directedWeight_edge_zero b lambda I p heq,
        directedQuadratic_edge_zero A B C I u b lambda epsilon p
          ((hAs.contDiffAt (capChartDomain_isOpen.mem_nhds (hT hp))).differentiableAt (by simp))
          ((hIs.contDiffAt (capChartDomain_isOpen.mem_nhds (hT hp))).differentiableAt (by simp)) heq]
      simp
  have hlow (p : Coord) (hp : p ∈ T) := hfixed p (hT hp)
  have hAvRaw (p : Coord) (hp : p ∈ T) : |G1 p*K p| ≤ M := by
    rw [←heightChartA_eq g z Y p]
    exact (hlow p hp).2.2.2.2.1
  have hAiRaw (p : Coord) (hp : p ∈ T) (i : Fin 2) : |coordPartial i (fun q => G1 q*K q) p| ≤ M := by
    rw [←hAeq]
    exact (hlow p hp).2.2.2.2.2.1 i
  have hi : (c2/2)*rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
      (directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda) ≤ RHS :=
    actual_cap_integrated_overlap_estimate hL hR hbottom (hbt.trans htop.le) hb hk hc1 hc2 hglow hM hMK
      hlambda.le heps.le heps1 hKs hG1s hBs hCs hIs hu hPDERaw hbackground hsupport
      (fun p hp => hOU (hmapO (hT hp))) (fun p hp => hdisp p (hT hp))
      (fun p hp => (hlow p hp).2.1) (fun p hp => (hlow p hp).2.2.1)
      (fun p hp => (hlow p hp).1) hAvRaw hAiRaw
      (fun p hp => (hlow p hp).2.2.2.2.2.2.1) (fun p hp => (hlow p hp).2.2.2.2.2.2.2)
      (fun p hp => (hlow p hp).2.2.2.1) hcoerceClosed
  have hinterior := capInterior_gradient_le_directed_energy hL hR hbottom hLR hbt htop hb
    hlambda.le hIs hu (fun p hp => (hfixed p (hS hp)).2.1)
  have hWpos : 0 < capInteriorWeightFloor top b lambda MI := capInteriorWeightFloor_pos htop
  have hden : 0 < c2/2 := by positivity
  have henergy : rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
      (directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda) ≤ (2/c2)*RHS := by
    have hh : rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
        (directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda) ≤ RHS/(c2/2) :=
      (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hi)
    have hscale (value : ℝ) : value/(c2/2) = (2/c2)*value := by
      rw [div_div_eq_mul_div, div_mul_eq_mul_div, mul_comm]
    rw [hscale RHS] at hh
    exact hh
  have hfinal := hinterior.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  change rectangleIntegral L R bottom top (fun p => (coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤ _
  have hscale : (1/capInteriorWeightFloor top b lambda MI)*(2/c2) =
      2/(c2*capInteriorWeightFloor top b lambda MI) := by
    rw [div_mul_div_comm, one_mul, mul_comm (capInteriorWeightFloor top b lambda MI)]
  calc
    _ ≤ (1/capInteriorWeightFloor top b lambda MI)*((2/c2)*RHS) := hfinal
    _ = (2/(c2*capInteriorWeightFloor top b lambda MI))*RHS := by rw [←mul_assoc,hscale]
    _ = _ := rfl

end SmoothLocal.Flow

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Flow.exists_uniform_original_data_actual_high_cap_estimate := @OAI.SmoothLocal.Flow.exists_uniform_original_data_actual_high_cap_estimate
