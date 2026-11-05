-- Prove2me | solution 1 for OAI.SmoothLocal.Flow.patch_actual_directed_near_coercivity
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:31:29.880192+00:00
-- url     : https://prove2.me/submissions/99d9be54-8b5d-4b19-8548-2d39b26b2c56

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

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
namespace SmoothLocal.Weighted

theorem normalized_T_lower_bound {H Is epsilon t B MI Mt MB : ℝ}
    (heps : 0 ≤ epsilon) (hMt : 0 ≤ Mt) (hIs : |Is| ≤ MI)
    (ht : |t| ≤ Mt) (hB : |B| ≤ MB)
    (hbudget : 2 * (MI + epsilon + epsilon * Mt * MB) ≤ H) :
    H / 4 ≤ (H - Is - epsilon + epsilon * t * B) / 2 := by
  have hprod : |epsilon * t * B| ≤ epsilon * Mt * MB := by
    rw [abs_mul, abs_mul, abs_of_nonneg heps]
    exact mul_le_mul (mul_le_mul_of_nonneg_left ht heps) hB
      (abs_nonneg B) (mul_nonneg heps hMt)
  have hlower := (abs_le.mp hprod).1
  have hupper := (abs_le.mp hIs).2
  linarith

theorem quadratic_cross_absorption {T S J u v : ℝ} (hT : 0 < T) :
    T / 2 * u ^ 2 + (S - J ^ 2 / (2 * T)) * v ^ 2 ≤
      T * u ^ 2 + S * v ^ 2 + J * u * v := by
  have hs : 0 ≤ (T * u + J * v) ^ 2 / (2 * T) :=
    div_nonneg (sq_nonneg _) (by positivity)
  have he : T * u ^ 2 + S * v ^ 2 + J * u * v -
      (T / 2 * u ^ 2 + (S - J ^ 2 / (2 * T)) * v ^ 2) =
      (T * u + J * v) ^ 2 / (2 * T) := by
    field_simp
    ring
  linarith

theorem cross_loss_bound {T J W H A C epsilon : ℝ}
    (hW : 0 < W) (hH : 0 < H) (hC : 0 ≤ C) (heps : 0 ≤ epsilon)
    (hT : W * H / 4 ≤ T)
    (hJ : |J| ≤ W * C * epsilon * (1 + H * |A|)) :
    J ^ 2 / (T * W) ≤
      8 * C ^ 2 * epsilon ^ 2 * (H⁻¹ + H * A ^ 2) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hmajor : 0 ≤ W * C * epsilon * (1 + H * |A|) := by positivity
  have hj2 : J ^ 2 ≤ (W * C * epsilon * (1 + H * |A|)) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg J) hmajor).mpr hJ
  have hshape : (1 + H * |A|) ^ 2 ≤ 2 * (1 + H ^ 2 * A ^ 2) := by
    nlinarith [sq_nonneg (H * |A| - 1), sq_abs A]
  have hnum : J ^ 2 ≤ 2 * W ^ 2 * C ^ 2 * epsilon ^ 2 * (1 + H ^ 2 * A ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hshape (sq_nonneg (W * C * epsilon))
    nlinarith [hj2]
  have hden : W ^ 2 * H / 4 ≤ T * W := by
    have hm := mul_le_mul_of_nonneg_right hT hW.le
    nlinarith [hm]
  have hR : 0 ≤ 8 * C ^ 2 * epsilon ^ 2 * (H⁻¹ + H * A ^ 2) := by positivity
  apply (div_le_iff₀ (mul_pos hTpos hW)).mpr
  have hm := mul_le_mul_of_nonneg_left hden hR
  have he : (8 * C ^ 2 * epsilon ^ 2 * (H⁻¹ + H * A ^ 2)) *
      (W ^ 2 * H / 4) =
      2 * W ^ 2 * C ^ 2 * epsilon ^ 2 * (1 + H ^ 2 * A ^ 2) := by
    field_simp
    ring
  rw [he] at hm
  exact hnum.trans hm

end SmoothLocal.Weighted

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
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Model
open SmoothLocal.Geometry

theorem squareTransition_contDiff : ContDiff ℝ ∞ squareTransition :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem squareTransition_range (t : ℝ) :
    0 ≤ squareTransition t ∧ squareTransition t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem squareTransition_zero {t : ℝ} (ht : t ≤ 1 / 4) : squareTransition t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem squareTransition_one {t : ℝ} (ht : 1 / 2 ≤ t) : squareTransition t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem squareTransition_monotone : Monotone squareTransition := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

theorem squareTransition_deriv_nonneg (t : ℝ) : 0 ≤ deriv squareTransition t :=
  squareTransition_monotone.deriv_nonneg

theorem modelProfile_contDiff : ContDiff ℝ ∞ modelProfile :=
  contDiff_const.sub ((contDiff_id.pow 2).mul
    (squareTransition_contDiff.comp (contDiff_id.pow 2)))

theorem modelProfile_bounds (y : ℝ) : 1 - y ^ 2 ≤ modelProfile y ∧ modelProfile y ≤ 1 := by
  have hh := squareTransition_range (y ^ 2)
  have hprod := mul_le_mul_of_nonneg_left hh.2 (sq_nonneg y)
  have hprod0 := mul_nonneg (sq_nonneg y) hh.1
  unfold modelProfile
  constructor <;> nlinarith

theorem modelProfile_hasDerivAt (y : ℝ) :
    HasDerivAt modelProfile
      (-2 * y * squareTransition (y ^ 2) - 2 * y ^ 3 * deriv squareTransition (y ^ 2)) y := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    convert (hasDerivAt_id y).pow 2 using 1 <;> first | rfl | simp
  have hcut := ((squareTransition_contDiff.differentiable (by simp)) (y ^ 2)).hasDerivAt.comp y hsq
  have hp := (hsq.mul hcut).const_sub 1
  convert hp using 1 <;> first | rfl | (dsimp only [Function.comp_def]; ring)

theorem modelProfile_deriv (y : ℝ) :
    deriv modelProfile y =
      -2 * y * squareTransition (y ^ 2) - 2 * y ^ 3 * deriv squareTransition (y ^ 2) :=
  (modelProfile_hasDerivAt y).deriv

theorem modelCurvature_contDiff (kappa : ℝ) : ContDiff ℝ ∞ (modelCurvature kappa) :=
  contDiff_const.mul (((contDiff_apply ℝ ℝ 0).pow 2).sub
    (modelProfile_contDiff.comp (contDiff_apply ℝ ℝ 1)))

end SmoothLocal.Model

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
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def weightH0 (b lambda : ℝ) (p : Coord) : ℝ := lambda + 8 / edgeDistance b p

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

theorem directedWeight_partial_t
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    coordPartial 0 (directedWeight b lambda I) p =
      directedWeight b lambda I p * coordPartial 0 I p := by
  simpa using directedWeight_partial b lambda hI 0

theorem directedWeight_partial_s
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    coordPartial 1 (directedWeight b lambda I) p =
      -8 * (edgeDistance b p) ^ 7 * Real.exp (weightPhase lambda I p) +
        directedWeight b lambda I p * (coordPartial 1 I p - lambda) := by
  simpa using directedWeight_partial b lambda hI 1

theorem directedWeight_partial_s_factored
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) (hd : edgeDistance b p ≠ 0) :
    coordPartial 1 (directedWeight b lambda I) p =
      directedWeight b lambda I p * (-weightH0 b lambda p + coordPartial 1 I p) := by
  rw [directedWeight_partial_s b lambda hI]
  unfold directedWeight weightH0
  field_simp [hd]
  ring

theorem directedWeight_pos (b lambda : ℝ) (I : Coord → ℝ) (p : Coord) (hp : p 1 < b) :
    0 < directedWeight b lambda I p :=
  mul_pos (pow_pos (sub_pos.mpr hp) 8) (Real.exp_pos _)

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

theorem directed_coefficients
    (A B C : Coord → ℝ) (b lambda epsilon : ℝ)
    (hA : DifferentiableAt ℝ A p) (hI : DifferentiableAt ℝ I p)
    (hd : edgeDistance b p ≠ 0) :
    multiplierT B (directedM b lambda I) (directedN b lambda epsilon I) p =
      directedWeight b lambda I p *
        ((weightH0 b lambda p - coordPartial 1 I p - epsilon +
          epsilon * p 0 * (2 * B p - coordPartial 0 I p)) / 2) ∧
    multiplierS A C (directedM b lambda I) (directedN b lambda epsilon I) p =
      directedWeight b lambda I p *
        (coordPartial 1 A p / 2 - weightH0 b lambda p * A p / 2 +
          epsilon * p 0 * coordPartial 0 A p / 2 - C p +
          A p * (coordPartial 1 I p + epsilon + epsilon * p 0 * coordPartial 0 I p) / 2) ∧
    multiplierJ A B C (directedM b lambda I) (directedN b lambda epsilon I) p =
      directedWeight b lambda I p *
        (coordPartial 0 I p - B p + epsilon * p 0 *
          (C p - coordPartial 1 A p + A p * (weightH0 b lambda p - coordPartial 1 I p))) := by
  have hm := directedM_differentiableAt b lambda hI
  have hn := directedN_differentiableAt b lambda epsilon hI
  have hwt := directedWeight_partial_t b lambda hI
  have hws := directedWeight_partial_s_factored b lambda hI hd
  constructor
  · unfold multiplierT
    rw [directedM_partial, directedN_partial b lambda epsilon hI]
    simp only [Fin.isValue, ↓reduceIte, mul_one, hwt, hws, directedN]
    ring
  constructor
  · unfold multiplierS
    rw [HessianCalculus.coordPartial_mul_at hA hm 1,
      HessianCalculus.coordPartial_mul_at hA hn 0,
      directedM_partial, directedN_partial b lambda epsilon hI]
    simp only [Fin.isValue, ↓reduceIte, mul_one, hwt, hws, directedM, directedN]
    ring
  · unfold multiplierJ
    rw [HessianCalculus.coordPartial_mul_at hA hn 1,
      directedM_partial, directedN_partial b lambda epsilon hI]
    have h01 : ¬((0 : Fin 2) = 1) := by decide
    simp only [Fin.isValue, h01, ↓reduceIte, mul_zero, zero_mul, zero_add,
      hwt, hws, directedM, directedN]
    ring

theorem directedS_transverse_expansion
    (A B C : Coord → ℝ) (b lambda epsilon : ℝ) (ell : ℕ) (r : ℝ)
    (hA : DifferentiableAt ℝ A p) (hI : DifferentiableAt ℝ I p)
    (hd : edgeDistance b p ≠ 0)
    (hC : C p = ((ell : ℝ) + 1) * coordPartial 1 A p + A p * r) :
    multiplierS A C (directedM b lambda I) (directedN b lambda epsilon I) p =
      directedWeight b lambda I p *
        (-((ell : ℝ) + 1 / 2) * coordPartial 1 A p +
          epsilon * p 0 * coordPartial 0 A p / 2 - weightH0 b lambda p * A p / 2 +
          A p * ((coordPartial 1 I p + epsilon + epsilon * p 0 * coordPartial 0 I p) / 2 - r)) := by
  rw [(directed_coefficients A B C b lambda epsilon hA hI hd).2.1, hC]
  ring

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

theorem eventuallyEq_zero_of_not_mem_tsupport
    {V : Type*} [Zero V] (f : Coord → V) {p : Coord} (hp : p ∉ tsupport f) :
    f =ᶠ[𝓝 p] 0 := by
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hp] with q hq
  change f q = 0
  by_contra hne
  exact hq (subset_tsupport f hne)

theorem metric_coeff_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (i j : Fin 2) :
    (fun q => g q i j) =ᶠ[𝓝 p] (fun q => h q i j) :=
  heq.mono fun _ hq => congrFun (congrFun hq i) j

theorem christoffel_eq_of_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (k i j : Fin 2) :
    christoffel g k i j p = christoffel h k i j p := by
  have hval := heq.self_of_nhds
  have hd (a b c : Fin 2) : coordPartial a (fun q => g q b c) p =
      coordPartial a (fun q => h q b c) p :=
    coordPartial_eq_of_eventuallyEq (metric_coeff_eventuallyEq heq b c) a
  simp only [christoffel, inverseMetric, hval, hd]

theorem christoffel_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (k i j : Fin 2) :
    christoffel g k i j =ᶠ[𝓝 p] christoffel h k i j :=
  heq.eventuallyEq_nhds.mono fun _ hq => christoffel_eq_of_eventuallyEq hq k i j

theorem riemann_eq_of_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (l k i j : Fin 2) :
    riemann g l k i j p = riemann h l k i j p := by
  have hΓ := christoffel_eq_of_eventuallyEq heq
  have hd (a b c d : Fin 2) : coordPartial a (christoffel g b c d) p =
      coordPartial a (christoffel h b c d) p :=
    coordPartial_eq_of_eventuallyEq (christoffel_eventuallyEq heq b c d) a
  simp only [riemann, hΓ, hd]

theorem gaussianCurvature_eq_of_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) : gaussianCurvature g p = gaussianCurvature h p := by
  simp only [gaussianCurvature, heq.self_of_nhds, riemann_eq_of_eventuallyEq heq]

theorem metric_add_eventuallyEq_of_not_mem_tsupport (g η : MetricField)
    {p : Coord} (hp : p ∉ tsupport η) : g + η =ᶠ[𝓝 p] g := by
  filter_upwards [eventuallyEq_zero_of_not_mem_tsupport η hp] with q hq
  change g q + η q = g q
  simp only [hq, Pi.zero_apply, add_zero]

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
open SmoothLocal.Model

theorem patchBox_subset_centralBox : patchBox ⊆ centralBox := by
  intro p hp
  constructor <;> intro i <;> linarith [hp.1 i, hp.2 i]

theorem gaussianCurvature_eventuallyEq_of_metric_eventuallyEq
    {g h : MetricField} {p : Coord} (heq : g =ᶠ[𝓝 p] h) :
    gaussianCurvature g =ᶠ[𝓝 p] gaussianCurvature h := by
  filter_upwards [heq.eventuallyEq_nhds] with q hq
  exact gaussianCurvature_eq_of_eventuallyEq hq

theorem patch_smallCurvature_eventually_model
    {g0 eta : MetricField} {kappa : ℝ} {U : Set Coord}
    (hk : 0 < kappa) (hU : IsOpen U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    {p : Coord} (hp : p ∈ U)
    (hsmall : |gaussianCurvature (g0 + eta) p| ≤ kappa / 8) :
    gaussianCurvature (g0 + eta) =ᶠ[𝓝 p] modelCurvature kappa := by
  have hout : p ∉ patchBox := by
    intro hin
    have hneg := hcentral p (patchBox_subset_centralBox hin)
    have hlo := (abs_le.mp hsmall).1
    linarith
  have hts : p ∉ tsupport eta := fun hin => hout (hsupport hin)
  have hsame := gaussianCurvature_eventuallyEq_of_metric_eventuallyEq
    (metric_add_eventuallyEq_of_not_mem_tsupport g0 eta hts)
  have hmodel : gaussianCurvature g0 =ᶠ[𝓝 p] modelCurvature kappa := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hbackground q hq
  exact hsame.trans hmodel

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

variable {U : Set Coord}

end SmoothLocal.Weighted

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

theorem primitive_directedJ
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    {p : Coord} (hp : p ∈ coordinateRectangle R a b)
    (A C : Coord → ℝ) (hA : DifferentiableAt ℝ A p)
    (edge lambda epsilon : ℝ) (hd : edgeDistance edge p ≠ 0) :
    multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
      (directedN edge lambda epsilon (coordinatePrimitive B)) p =
      directedWeight edge lambda (coordinatePrimitive B) p *
        (epsilon * p 0 * (C p - coordPartial 1 A p +
          A p * (weightH0 edge lambda p - coordPartial 1 (coordinatePrimitive B) p))) := by
  have hI : DifferentiableAt ℝ (coordinatePrimitive B) p :=
    ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by simp)
  have he := (directed_coefficients A B C edge lambda epsilon hA hI hd).2.2
  rw [coordinatePrimitive_partial_t hB hR hp] at he
  simpa only [sub_self, zero_add] using he

end SmoothLocal.Weighted

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

theorem coordinatePoint_mem_modelSquare {t y : ℝ}
    (ht : t ∈ Icc (-3 : ℝ) 3) (hy : y ∈ Icc (-3 : ℝ) 3) :
    coordinatePoint t y ∈ modelSquare := by
  simp only [mem_Icc] at ht hy
  constructor <;> intro i <;> fin_cases i <;> simp [coordinatePoint] <;> tauto

variable {q : Coord → ℝ} {U : Set Coord}

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff
namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

variable {B : Coord → ℝ} {R a b : ℝ} {p : Coord}

theorem primitive_directedT_lower_bound
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (edge lambda epsilon MI MB : ℝ)
    (heps : 0 ≤ epsilon) (hedge : p 1 < edge)
    (hIs : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI)
    (hBp : |B p| ≤ MB)
    (hlambda : 2 * (MI + epsilon + epsilon * R * MB) ≤ lambda) :
    directedWeight edge lambda (coordinatePrimitive B) p * weightH0 edge lambda p / 4 ≤
      multiplierT B (directedM edge lambda (coordinatePrimitive B))
        (directedN edge lambda epsilon (coordinatePrimitive B)) p := by
  have hI : DifferentiableAt ℝ (coordinatePrimitive B) p :=
    ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by simp)
  have hd : 0 < edgeDistance edge p := sub_pos.mpr hedge
  have hH : lambda ≤ weightH0 edge lambda p := by
    unfold weightH0
    exact le_add_of_nonneg_right (div_nonneg (by norm_num) hd.le)
  have hbound := normalized_T_lower_bound heps hR.le hIs
    (abs_lt.mpr hp.1).le hBp (hlambda.trans hH)
  have hW := (directedWeight_pos edge lambda (coordinatePrimitive B) p hedge).le
  have hcoeff := (directed_coefficients (fun _ => 0) B (fun _ => 0)
    edge lambda epsilon (differentiableAt_const (0 : ℝ)) hI hd.ne').1
  rw [coordinatePrimitive_partial_t hB hR hp] at hcoeff
  rw [hcoeff]
  have hm := mul_le_mul_of_nonneg_left hbound hW
  nlinarith only [hm]

theorem primitive_directedJ_bound
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (A C : Coord → ℝ)
    (hA : DifferentiableAt ℝ A p) (edge lambda epsilon MCA MA MI : ℝ)
    (heps : 0 ≤ epsilon) (hedge : p 1 < edge) (hH : 0 ≤ weightH0 edge lambda p)
    (hCA : |C p - coordPartial 1 A p| ≤ MCA)
    (hAp : |A p| ≤ MA) (hIs : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI) :
    |multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
      (directedN edge lambda epsilon (coordinatePrimitive B)) p| ≤
      directedWeight edge lambda (coordinatePrimitive B) p * epsilon * R *
        (MCA + MA * MI + weightH0 edge lambda p * |A p|) := by
  have hd : 0 < edgeDistance edge p := sub_pos.mpr hedge
  have hW := (directedWeight_pos edge lambda (coordinatePrimitive B) p hedge).le
  have hMA : 0 ≤ MA := (abs_nonneg _).trans hAp
  have hMI : 0 ≤ MI := (abs_nonneg _).trans hIs
  have hprod : |A p * coordPartial 1 (coordinatePrimitive B) p| ≤ MA * MI := by
    rw [abs_mul]
    exact mul_le_mul hAp hIs (abs_nonneg _) hMA
  have hinner : |C p - coordPartial 1 A p +
      A p * (weightH0 edge lambda p - coordPartial 1 (coordinatePrimitive B) p)| ≤
      MCA + MA * MI + weightH0 edge lambda p * |A p| := by
    have he : C p - coordPartial 1 A p +
        A p * (weightH0 edge lambda p - coordPartial 1 (coordinatePrimitive B) p) =
        (C p - coordPartial 1 A p) - A p * coordPartial 1 (coordinatePrimitive B) p +
          weightH0 edge lambda p * A p := by ring
    rw [he]
    calc
      _ ≤ |(C p - coordPartial 1 A p) - A p * coordPartial 1 (coordinatePrimitive B) p| +
          |weightH0 edge lambda p * A p| := abs_add_le _ _
      _ ≤ (|C p - coordPartial 1 A p| +
          |A p * coordPartial 1 (coordinatePrimitive B) p|) +
          |weightH0 edge lambda p * A p| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ _ := by
        rw [abs_mul (weightH0 edge lambda p) (A p), abs_of_nonneg hH]
        exact add_le_add (add_le_add hCA hprod) le_rfl
  rw [primitive_directedJ hB hR hp A C hA edge lambda epsilon hd.ne']
  simp only [abs_mul, abs_of_nonneg hW, abs_of_nonneg heps]
  have ht : |p 0| ≤ R := (abs_lt.mpr hp.1).le
  have hm := mul_le_mul ht hinner (abs_nonneg _) hR.le
  have hm' := mul_le_mul_of_nonneg_left hm (mul_nonneg hW heps)
  nlinarith only [hm']

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

def directedPrincipal (A : Coord → ℝ) (ell : ℕ) (epsilon : ℝ) (p : Coord) : ℝ :=
  -((ell : ℝ) + 1 / 2) * coordPartial 1 A p + epsilon * p 0 * coordPartial 0 A p / 2

def directedSResidual (B r : Coord → ℝ) (_ : ℕ) (epsilon : ℝ) (p : Coord) : ℝ :=
  (coordPartial 1 (coordinatePrimitive B) p + epsilon + epsilon * p 0 * B p) / 2 - r p

theorem primitive_directedS_expansion
    {B : Coord → ℝ} {R a b : ℝ} {p : Coord}
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (A C r : Coord → ℝ)
    (hA : DifferentiableAt ℝ A p) (edge lambda epsilon : ℝ) (ell : ℕ)
    (hedge : p 1 < edge)
    (hC : C p = ((ell : ℝ) + 1) * coordPartial 1 A p + A p * r p) :
    multiplierS A C (directedM edge lambda (coordinatePrimitive B))
      (directedN edge lambda epsilon (coordinatePrimitive B)) p =
      directedWeight edge lambda (coordinatePrimitive B) p *
        (directedPrincipal A ell epsilon p - weightH0 edge lambda p * A p / 2 +
          A p * directedSResidual B r ell epsilon p) := by
  have hI : DifferentiableAt ℝ (coordinatePrimitive B) p :=
    ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by simp)
  rw [directedS_transverse_expansion A B C edge lambda epsilon ell (r p) hA hI
    (sub_pos.mpr hedge).ne' hC, coordinatePrimitive_partial_t hB hR hp]
  rfl

theorem directedSResidual_bound {B r : Coord → ℝ} {ell : ℕ} {epsilon R MI MB Mr : ℝ}
    {p : Coord} (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (hR : 0 ≤ R)
    (ht : |p 0| ≤ R) (hI : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI)
    (hB : |B p| ≤ MB) (hr : |r p| ≤ Mr) :
    |directedSResidual B r ell epsilon p| ≤ (MI + 1 + R * MB) / 2 + Mr := by
  have hMB : 0 ≤ MB := (abs_nonneg _).trans hB
  have hprod : |epsilon * p 0 * B p| ≤ R * MB := by
    rw [abs_mul, abs_mul, abs_of_nonneg heps]
    have het : epsilon * |p 0| ≤ R :=
      (mul_le_mul_of_nonneg_left ht heps).trans (by nlinarith)
    exact (mul_le_mul het hB (abs_nonneg _) hR)
  unfold directedSResidual
  calc
    _ ≤ |(coordPartial 1 (coordinatePrimitive B) p + epsilon + epsilon * p 0 * B p) / 2| +
        |r p| := abs_sub _ _
    _ = |coordPartial 1 (coordinatePrimitive B) p + epsilon + epsilon * p 0 * B p| / 2 +
        |r p| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ ((|coordPartial 1 (coordinatePrimitive B) p| + |epsilon|) +
        |epsilon * p 0 * B p|) / 2 + |r p| := by
      have hsum : |coordPartial 1 (coordinatePrimitive B) p + epsilon + epsilon * p 0 * B p| ≤
          (|coordPartial 1 (coordinatePrimitive B) p| + |epsilon|) + |epsilon * p 0 * B p| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      exact add_le_add (div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
    _ ≤ (MI + 1 + R * MB) / 2 + Mr := by rw [abs_of_nonneg heps]; linarith

theorem normalized_loss_budget {H A MA L mu : ℝ}
    (hH : 0 < H) (hL : 0 ≤ L) (hA : |A| ≤ MA)
    (hsmall : L * MA ≤ 1 / 8) (hloss : L / H ≤ mu / 4) :
    L * (H⁻¹ + H * A ^ 2) ≤ mu / 4 + H * |A| / 8 := by
  have hLA : L * |A| ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left hA hL).trans hsmall
  have hLA2 : L * A ^ 2 ≤ |A| / 8 := by
    have hm := mul_le_mul_of_nonneg_right hLA (abs_nonneg A)
    nlinarith [sq_abs A]
  have hmul := mul_le_mul_of_nonneg_left hLA2 hH.le
  calc
    _ = L / H + H * (L * A ^ 2) := by ring
    _ ≤ mu / 4 + H * (|A| / 8) := add_le_add hloss hmul
    _ = _ := by ring

theorem residual_abs_error_bound {A e E H : ℝ}
    (he : |e| ≤ E) (hEH : E ≤ H / 8) :
    -(H * |A| / 8) ≤ A * e := by
  have habs : |A * e| ≤ H * |A| / 8 := by
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_left (he.trans hEH) (abs_nonneg A)
    nlinarith only [h]
  exact (abs_le.mp habs).1

theorem normalized_negative_near_coercivity {H A MA L mu Q e E : ℝ}
    (hH : 0 < H) (hL : 0 ≤ L) (hmu : 0 < mu) (hA : A ≤ 0) (hAM : |A| ≤ MA)
    (hsmall : L * MA ≤ 1 / 8) (hloss : L / H ≤ mu / 4)
    (he : |e| ≤ E) (hEH : E ≤ H / 8) (hQ : mu ≤ Q) :
    mu / 2 + H * |A| / 4 ≤ Q - H * A / 2 + A * e - L * (H⁻¹ + H * A ^ 2) := by
  have hcross := normalized_loss_budget hH hL hAM hsmall hloss
  have herr := residual_abs_error_bound (A := A) he hEH
  rw [abs_of_nonpos hA] at *
  nlinarith

theorem normalized_positive_strip_coercivity {H A MA L mu Q e E : ℝ}
    (hH : 0 < H) (hL : 0 ≤ L) (_ : 0 < mu) (hA : 0 ≤ A) (hAM : |A| ≤ MA)
    (hsmall : L * MA ≤ 1 / 8) (hloss : L / H ≤ mu / 4)
    (he : |e| ≤ E) (hEH : E ≤ H / 8) (hQ : mu ≤ Q) (hstrip : H * A ≤ mu / 3) :
    mu / 2 ≤ Q - H * A / 2 + A * e - L * (H⁻¹ + H * A ^ 2) := by
  have hcross := normalized_loss_budget hH hL hAM hsmall hloss
  have herr := residual_abs_error_bound (A := A) he hEH
  rw [abs_of_nonneg hA] at *
  nlinarith

theorem actual_quadratic_coercivity {T S J W H lambda mu Q e A L x y : ℝ}
    (hW : 0 < W) (hH : 0 < H) (_ : 0 < lambda) (_ : 0 < mu)
    (hlH : lambda ≤ H) (hT : W * H / 4 ≤ T)
    (hS : S = W * (Q - H * A / 2 + A * e))
    (hcross : J ^ 2 / (2 * T * W) ≤ L * (H⁻¹ + H * A ^ 2))
    (hmargin : mu / 2 ≤ Q - H * A / 2 + A * e - L * (H⁻¹ + H * A ^ 2)) :
    min (lambda / 8) (mu / 2) * W * (x ^ 2 + y ^ 2) ≤ T * x ^ 2 + S * y ^ 2 + J * x * y := by
  have hTpos : 0 < T := (show 0 < W * H / 4 by positivity).trans_le hT
  have hcross' : J ^ 2 / (2 * T) ≤ W * (L * (H⁻¹ + H * A ^ 2)) := by
    have hm := mul_le_mul_of_nonneg_right hcross hW.le
    have he : J ^ 2 / (2 * T * W) * W = J ^ 2 / (2 * T) := by
      field_simp [hTpos.ne', hW.ne']
    rw [he] at hm
    nlinarith only [hm]
  have hSlo : mu / 2 * W ≤ S - J ^ 2 / (2 * T) := by
    have hm := mul_le_mul_of_nonneg_left hmargin hW.le
    rw [hS]
    nlinarith only [hm, hcross']
  have hTlo : lambda / 8 * W ≤ T / 2 := by
    have hm := mul_le_mul_of_nonneg_left hlH hW.le
    nlinarith only [hm, hT]
  have hxlo : min (lambda / 8) (mu / 2) * W ≤ T / 2 :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hW.le).trans hTlo
  have hylo : min (lambda / 8) (mu / 2) * W ≤ S - J ^ 2 / (2 * T) :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hW.le).trans hSlo
  have hx := mul_le_mul_of_nonneg_right hxlo (sq_nonneg x)
  have hy := mul_le_mul_of_nonneg_right hylo (sq_nonneg y)
  have hq := quadratic_cross_absorption (S := S) (J := J) (u := x) (v := y) hTpos
  nlinarith only [hx, hy, hq]

theorem actual_normalized_cross_loss {T J W H A Cj epsilon : ℝ}
    (hW : 0 < W) (hH : 0 < H) (hCj : 0 ≤ Cj) (heps : 0 ≤ epsilon)
    (hT : W * H / 4 ≤ T)
    (hJ : |J| ≤ W * Cj * epsilon * (1 + H * |A|)) :
    J ^ 2 / (2 * T * W) ≤ 4 * Cj ^ 2 * epsilon ^ 2 * (H⁻¹ + H * A ^ 2) := by
  have hh := cross_loss_bound hW hH hCj heps hT hJ
  have hTpos : 0 < T := (show 0 < W * H / 4 by positivity).trans_le hT
  have he : J ^ 2 / (2 * T * W) = (J ^ 2 / (T * W)) / 2 := by
    field_simp [hTpos.ne', hW.ne']
  rw [he]
  nlinarith only [hh]

theorem primitive_directed_near_coercivity
    {B : Coord → ℝ} {R a b : ℝ} {p : Coord}
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (A C r : Coord → ℝ)
    (hA : DifferentiableAt ℝ A p) (edge lambda epsilon : ℝ) (ell : ℕ)
    (hedge : p 1 < edge) (hlambda : 0 < lambda)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hC : C p = ((ell : ℝ) + 1) * coordPartial 1 A p + A p * r p)
    (MI MB Mr MA MAs mu : ℝ) (hmu : 0 < mu)
    (hIs : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI)
    (hBp : |B p| ≤ MB) (hr : |r p| ≤ Mr)
    (hAp : |A p| ≤ MA) (hAs : |coordPartial 1 A p| ≤ MAs)
    (hTbudget : 2 * (MI + epsilon + epsilon * R * MB) ≤ lambda)
    (hEbudget : (MI + 1 + R * MB) / 2 + Mr ≤ lambda / 8)
    (hsmall : 4 * (R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)) ^ 2 *
      epsilon ^ 2 * MA ≤ 1 / 8)
    (hloss : (4 * (R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)) ^ 2 *
      epsilon ^ 2) / lambda ≤ mu / 4)
    (hprincipal : mu ≤ directedPrincipal A ell epsilon p)
    (hstrip : 0 < A p → weightH0 edge lambda p * A p ≤ mu / 3)
    (x y : ℝ) :
    min (lambda / 8) (mu / 2) * directedWeight edge lambda (coordinatePrimitive B) p *
      (x ^ 2 + y ^ 2) ≤
      multiplierT B (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * x ^ 2 +
        multiplierS A C (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * y ^ 2 +
        multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * x * y := by
  let W := directedWeight edge lambda (coordinatePrimitive B) p
  let H := weightH0 edge lambda p
  let Cj := R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)
  let L := 4 * Cj ^ 2 * epsilon ^ 2
  let E := (MI + 1 + R * MB) / 2 + Mr
  have hMI : 0 ≤ MI := (abs_nonneg _).trans hIs
  have hMB : 0 ≤ MB := (abs_nonneg _).trans hBp
  have hMr : 0 ≤ Mr := (abs_nonneg _).trans hr
  have hMA : 0 ≤ MA := (abs_nonneg _).trans hAp
  have hMAs : 0 ≤ MAs := (abs_nonneg _).trans hAs
  have hCj : 0 ≤ Cj := by dsimp [Cj]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hW : 0 < W := directedWeight_pos _ _ _ _ hedge
  have hlH : lambda ≤ H := by
    dsimp [H, weightH0]
    exact le_add_of_nonneg_right (div_nonneg (by norm_num) (sub_pos.mpr hedge).le)
  have hH : 0 < H := hlambda.trans_le hlH
  have hCA : |C p - coordPartial 1 A p| ≤ (ell : ℝ) * MAs + MA * Mr := by
    have he : C p - coordPartial 1 A p =
        (ell : ℝ) * coordPartial 1 A p + A p * r p := by rw [hC]; ring
    rw [he]
    calc
      _ ≤ |(ell : ℝ) * coordPartial 1 A p| + |A p * r p| := abs_add_le _ _
      _ = (ell : ℝ) * |coordPartial 1 A p| + |A p| * |r p| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg ell)]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hAs (Nat.cast_nonneg ell))
        (mul_le_mul hAp hr (abs_nonneg _) hMA)
  have hT := primitive_directedT_lower_bound hB hR hp edge lambda epsilon MI MB
    heps hedge hIs hBp hTbudget
  have hJ0 := primitive_directedJ_bound hB hR hp A C hA edge lambda epsilon
    ((ell : ℝ) * MAs + MA * Mr) MA MI heps hedge hH.le hCA hAp hIs
  have hJ : |multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
      (directedN edge lambda epsilon (coordinatePrimitive B)) p| ≤
      W * Cj * epsilon * (1 + H * |A p|) := by
    refine hJ0.trans ?_
    have hD : 0 ≤ (ell : ℝ) * MAs + MA * Mr + MA * MI := by positivity
    have hh : 0 ≤ H * |A p| := mul_nonneg hH.le (abs_nonneg _)
    have hbase : (ell : ℝ) * MAs + MA * Mr + MA * MI + H * |A p| ≤
        ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1) * (1 + H * |A p|) := by
      nlinarith [mul_nonneg hD hh]
    have hm := mul_le_mul_of_nonneg_left hbase (mul_nonneg (mul_nonneg hW.le heps) hR.le)
    convert hm using 1
    dsimp only [W, H, Cj]
    ring
  have hcross := actual_normalized_cross_loss hW hH hCj heps hT hJ
  have he : |directedSResidual B r ell epsilon p| ≤ E :=
    directedSResidual_bound heps heps1 hR.le (abs_lt.mpr hp.1).le hIs hBp hr
  have hEH : E ≤ H / 8 := hEbudget.trans (by linarith)
  have hLH : L / H ≤ mu / 4 := by
    apply (div_le_iff₀ hH).2
    have hh : L ≤ (mu / 4) * lambda := (div_le_iff₀ hlambda).1 hloss
    exact hh.trans (mul_le_mul_of_nonneg_left hlH (by positivity))
  have hmargin : mu / 2 ≤ directedPrincipal A ell epsilon p - H * A p / 2 +
      A p * directedSResidual B r ell epsilon p - L * (H⁻¹ + H * (A p) ^ 2) := by
    by_cases hn : A p ≤ 0
    · have hh := normalized_negative_near_coercivity hH hL hmu hn hAp hsmall hLH he hEH hprincipal
      have hbonus : 0 ≤ H * |A p| / 4 := by positivity
      linarith
    · exact normalized_positive_strip_coercivity hH hL hmu (lt_of_not_ge hn).le hAp
        hsmall hLH he hEH hprincipal (hstrip (lt_of_not_ge hn))
  exact actual_quadratic_coercivity hW hH hlambda hmu hlH hT
    (primitive_directedS_expansion hB hR hp A C r hA edge lambda epsilon ell hedge hC)
    hcross hmargin

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Model

open SmoothLocal.Geometry SmoothLocal.Weighted

theorem squareTransition_deriv_zero_left {t : ℝ} (ht : t ≤ 1 / 4) :
    deriv squareTransition t = 0 := by
  have hmin : IsLocalMin squareTransition t := Filter.Eventually.of_forall (fun x => by
    rw [squareTransition_zero ht]
    exact (squareTransition_range x).1)
  exact hmin.deriv_eq_zero

theorem squareTransition_deriv_zero_right {t : ℝ} (ht : 1 / 2 ≤ t) :
    deriv squareTransition t = 0 := by
  have hmax : IsLocalMax squareTransition t := Filter.Eventually.of_forall (fun x => by
    rw [squareTransition_one ht]
    exact (squareTransition_range x).2)
  exact hmax.deriv_eq_zero

theorem modelProfile_deriv_outer {y : ℝ} (hy : 1 / 2 ≤ y ^ 2) :
    deriv modelProfile y = -2 * y := by
  rw [modelProfile_deriv, squareTransition_one hy, squareTransition_deriv_zero_right hy]
  ring

theorem modelProfile_deriv_nonneg_lower_cap {y : ℝ} (hy : y ≤ 1 / 50) :
    0 ≤ deriv modelProfile y := by
  by_cases hy0 : y ≤ 0
  · rw [modelProfile_deriv]
    have hy3 : y ^ 3 ≤ 0 := by
      have hh := mul_nonpos_of_nonpos_of_nonneg hy0 (sq_nonneg y)
      nlinarith only [hh]
    have hfirst : 0 ≤ -2 * y * squareTransition (y ^ 2) :=
      mul_nonneg (by linarith) (squareTransition_range _).1
    have hsecond : 0 ≤ -2 * y ^ 3 * deriv squareTransition (y ^ 2) :=
      mul_nonneg (by linarith) (squareTransition_deriv_nonneg _)
    linarith
  · have hypos : 0 < y := lt_of_not_ge hy0
    have hysq : y ^ 2 ≤ 1 / 4 :=
      (pow_le_pow_left₀ hypos.le hy 2).trans (by norm_num)
    rw [modelProfile_deriv, squareTransition_zero hysq, squareTransition_deriv_zero_left hysq]
    norm_num

theorem modelProfile_deriv_lower_three_quarters {y : ℝ} (hy : y ≤ -(3 / 4 : ℝ)) :
    3 / 2 ≤ deriv modelProfile y := by
  have hs : (3 / 4 : ℝ) ^ 2 ≤ (-y) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith : (3 / 4 : ℝ) ≤ -y) 2
  have hysq : 1 / 2 ≤ y ^ 2 := by nlinarith only [hs]
  rw [modelProfile_deriv_outer hysq]
  linarith

theorem modelProfile_middle_lower {y : ℝ}
    (hylo : -(3 / 4 : ℝ) ≤ y) (hyhi : y ≤ 1 / 50) :
    7 / 16 ≤ modelProfile y := by
  have hy2 : y ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := sq_le_sq' hylo (by linarith)
  nlinarith [(modelProfile_bounds y).1]

theorem modelCurvature_partial (kappa : ℝ) (p : Coord) (i : Fin 2) :
    coordPartial i (modelCurvature kappa) p =
      if i = 0 then 2 * kappa * p 0 else -kappa * deriv modelProfile (p 1) := by
  have hx := hasFDerivAt_apply (𝕜 := ℝ) 0 p
  have hy := ((modelProfile_contDiff.differentiable (by simp) (p 1)).hasDerivAt).comp_hasFDerivAt
    p (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hd := ((hx.pow 2).sub hy).const_mul kappa
  simp only [Function.comp_def, Pi.sub_def] at hd
  change fderiv ℝ (fun q : Coord => kappa * ((q 0) ^ 2 - modelProfile (q 1))) p
    (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;> simp
  ring

theorem modelCurvature_partial_y_nonpos {kappa : ℝ} (hkappa : 0 ≤ kappa)
    {p : Coord} (hy : p 1 ≤ 1 / 50) : coordPartial 1 (modelCurvature kappa) p ≤ 0 := by
  rw [modelCurvature_partial]
  norm_num only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hkappa)
    (modelProfile_deriv_nonneg_lower_cap hy)

theorem modelCurvature_negative_y_slope {kappa : ℝ} (hkappa : 0 ≤ kappa)
    {p : Coord} (hy : p 1 ≤ -(3 / 4 : ℝ)) :
    3 * kappa / 2 ≤ -coordPartial 1 (modelCurvature kappa) p := by
  rw [modelCurvature_partial]
  rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
  have hm := mul_le_mul_of_nonneg_left (modelProfile_deriv_lower_three_quarters hy) hkappa
  nlinarith only [hm]

theorem modelCurvature_middle_xsq_lower {kappa : ℝ} (hkappa : 0 < kappa)
    {p : Coord} (hylo : -(3 / 4 : ℝ) ≤ p 1) (hyhi : p 1 ≤ 1 / 50)
    (hK : |modelCurvature kappa p| ≤ kappa / 8) :
    5 / 16 ≤ (p 0) ^ 2 := by
  have hh := mul_le_mul_of_nonneg_left (modelProfile_middle_lower hylo hyhi) hkappa.le
  have hlower := (abs_le.mp hK).1
  unfold modelCurvature at hlower
  have hprod : kappa * (5 / 16) ≤ kappa * (p 0) ^ 2 := by nlinarith only [hh, hlower]
  exact le_of_mul_le_mul_left hprod hkappa

theorem directed_model_slope_lower {rho rhoMax epsilon R Mq t q : ℝ} (ell : ℕ)
    (hrho : 0 < rho) (hrhoMax : rho ≤ rhoMax) (heps : 0 ≤ epsilon)
    (ht : |t| ≤ R) (hq : |q| ≤ Mq)
    (hsmall : epsilon * R * Mq ≤ ((ell : ℝ) + 1 / 2) / rhoMax) :
    ((ell : ℝ) + 1 / 2) / (2 * rhoMax) ≤
      ((ell : ℝ) + 1 / 2) / rho + epsilon * t * q / 2 := by
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have hMq : 0 ≤ Mq := (abs_nonneg _).trans hq
  have hmax : 0 < rhoMax := hrho.trans_le hrhoMax
  have hbeta : 0 ≤ (ell : ℝ) + 1 / 2 := by positivity
  have hfrac : ((ell : ℝ) + 1 / 2) / rhoMax ≤ ((ell : ℝ) + 1 / 2) / rho :=
    (div_le_div_iff₀ hmax hrho).2 (mul_le_mul_of_nonneg_left hrhoMax hbeta)
  have hprod : |epsilon * t * q| ≤ epsilon * R * Mq := by
    rw [abs_mul, abs_mul, abs_of_nonneg heps]
    exact mul_le_mul (mul_le_mul_of_nonneg_left ht heps) hq
      (abs_nonneg _) (mul_nonneg heps hR)
  have hprodlo := (abs_le.mp (hprod.trans hsmall)).1
  have he : ((ell : ℝ) + 1 / 2) / (2 * rhoMax) =
      (((ell : ℝ) + 1 / 2) / rhoMax) / 2 := by ring
  rw [he]
  linarith

theorem model_geometric_principal_lower
    {kappa g0 G rho rhoMax epsilon R Mq q : ℝ} {p : Coord} (ell : ℕ)
    (hkappa : 0 < kappa) (hg0 : 0 < g0) (hG : g0 ≤ G)
    (hrho : 0 < rho) (hrhoMax : rho ≤ rhoMax) (heps : 0 < epsilon)
    (ht : |p 0| ≤ R) (hq : |q| ≤ Mq)
    (hsmall : epsilon * R * Mq ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hy : p 1 ≤ 1 / 50) (hK : |modelCurvature kappa p| ≤ kappa / 8) :
    modelCoercivityMargin g0 kappa rhoMax epsilon ell ≤
      G * (-(((ell : ℝ) + 1 / 2) / rho + epsilon * p 0 * q / 2) *
        coordPartial 1 (modelCurvature kappa) p + epsilon * kappa * (p 0) ^ 2) := by
  let beta : ℝ := (ell : ℝ) + 1 / 2
  let coef : ℝ := beta / rho + epsilon * p 0 * q / 2
  let amin : ℝ := beta / (2 * rhoMax)
  let base : ℝ := coef * (-coordPartial 1 (modelCurvature kappa) p) + epsilon * kappa * (p 0) ^ 2
  have hmax : 0 < rhoMax := hrho.trans_le hrhoMax
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hamin : 0 < amin := by dsimp [amin]; positivity
  have hcoef : amin ≤ coef := directed_model_slope_lower ell hrho hrhoMax heps.le ht hq hsmall
  have hKy : 0 ≤ -coordPartial 1 (modelCurvature kappa) p :=
    neg_nonneg.mpr (modelCurvature_partial_y_nonpos hkappa.le hy)
  have hterm : 0 ≤ epsilon * kappa * (p 0) ^ 2 := by positivity
  have hbase : 0 ≤ base := by dsimp [base]; exact add_nonneg (mul_nonneg (hamin.le.trans hcoef) hKy) hterm
  have hlower : kappa * min (3 * beta / (4 * rhoMax)) (5 * epsilon / 16) ≤ base := by
    by_cases hylo : p 1 ≤ -(3 / 4 : ℝ)
    · have hslope := modelCurvature_negative_y_slope hkappa.le hylo
      calc
        _ ≤ kappa * (3 * beta / (4 * rhoMax)) := mul_le_mul_of_nonneg_left (min_le_left _ _) hkappa.le
        _ = amin * (3 * kappa / 2) := by dsimp [amin]; ring
        _ ≤ amin * (-coordPartial 1 (modelCurvature kappa) p) :=
          mul_le_mul_of_nonneg_left hslope hamin.le
        _ ≤ coef * (-coordPartial 1 (modelCurvature kappa) p) := mul_le_mul_of_nonneg_right hcoef hKy
        _ ≤ base := by dsimp [base]; linarith
    · have hxsq := modelCurvature_middle_xsq_lower hkappa (lt_of_not_ge hylo).le hy hK
      calc
        _ ≤ kappa * (5 * epsilon / 16) := mul_le_mul_of_nonneg_left (min_le_right _ _) hkappa.le
        _ = epsilon * kappa * (5 / 16) := by ring
        _ ≤ epsilon * kappa * (p 0) ^ 2 := mul_le_mul_of_nonneg_left hxsq (mul_pos heps hkappa).le
        _ ≤ base := by
          dsimp [base]
          have hn := mul_nonneg (hamin.le.trans hcoef) hKy
          linarith
  have hfirst := mul_le_mul_of_nonneg_left hlower hg0.le
  have hsecond := mul_le_mul_of_nonneg_right hG hbase
  unfold modelCoercivityMargin
  dsimp only [base, coef, beta] at hfirst hsecond
  nlinarith only [hfirst, hsecond]

end SmoothLocal.Model

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Model
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem modelPrincipal_derivative_remainder_bound
    {G : Coord → ℝ} {p : Coord} (ell : ℕ) {epsilon R MG : ℝ}
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (ht : |p 0| ≤ R)
    (hGs : |coordPartial 1 G p| ≤ MG) (hGt : |coordPartial 0 G p| ≤ MG) :
    |-((ell : ℝ) + 1 / 2) * coordPartial 1 G p +
      epsilon * p 0 * coordPartial 0 G p / 2| ≤ modelPrincipalRemainderBound ell R MG := by
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have hMG : 0 ≤ MG := (abs_nonneg _).trans hGs
  have hbeta : 0 ≤ (ell : ℝ) + 1 / 2 := by positivity
  have hfirst : |-((ell : ℝ) + 1 / 2) * coordPartial 1 G p| ≤
      ((ell : ℝ) + 1 / 2) * MG := by
    rw [abs_mul, abs_neg, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left hGs hbeta
  have hprod : |epsilon * p 0 * coordPartial 0 G p| ≤ R * MG := by
    rw [abs_mul, abs_mul, abs_of_nonneg heps]
    have het : epsilon * |p 0| ≤ R :=
      (mul_le_mul_of_nonneg_left ht heps).trans (by nlinarith)
    exact mul_le_mul het hGt (abs_nonneg _) hR
  have hsecond : |epsilon * p 0 * coordPartial 0 G p / 2| ≤ R * MG / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right hprod (by norm_num)
  have hsum := (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  unfold modelPrincipalRemainderBound
  nlinarith only [hsum]

theorem modelPrincipal_radius_error
    {g0 kappa rhoMax epsilon R MG K : ℝ} (ell : ℕ)
    (hg0 : 0 < g0) (hkappa : 0 < kappa) (hrho : 0 < rhoMax) (heps : 0 < epsilon)
    (hR : 0 ≤ R) (hMG : 0 ≤ MG)
    (hK : |K| ≤ modelPrincipalRadius g0 kappa rhoMax epsilon R MG ell) :
    |K| * modelPrincipalRemainderBound ell R MG ≤
      modelCoercivityMargin g0 kappa rhoMax epsilon ell / 2 := by
  let mu := modelCoercivityMargin g0 kappa rhoMax epsilon ell
  let M := modelPrincipalRemainderBound ell R MG
  have hmu : 0 < mu := modelCoercivityMargin_pos ell hg0 hkappa hrho heps
  have hM : 0 ≤ M := modelPrincipalRemainderBound_nonneg ell hR hMG
  have hden : 0 < 2 * (M + 1) := by positivity
  have hK' : |K| ≤ mu / (2 * (M + 1)) := hK.trans (min_le_right _ _)
  calc
    _ ≤ mu / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right hK' hM
    _ ≤ mu / (2 * (M + 1)) * (M + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_pos hmu hden).le
    _ = mu / 2 := by field_simp [show M + 1 ≠ 0 by positivity]

theorem model_full_principal_lower
    {G K : Coord → ℝ} {p : Coord} {y kappa g0 rho rhoMax epsilon R MG Mq q : ℝ}
    (ell : ℕ) (hGdiff : DifferentiableAt ℝ G p) (hKdiff : DifferentiableAt ℝ K p)
    (hkappa : 0 < kappa) (hg0 : 0 < g0) (hG : g0 ≤ G p)
    (hrho : 0 < rho) (hrhoMax : rho ≤ rhoMax) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (ht : |p 0| ≤ R) (hq : |q| ≤ Mq)
    (hsmall : epsilon * R * Mq ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hy : y ≤ 1 / 50)
    (hGsi : |coordPartial 1 G p| ≤ MG) (hGti : |coordPartial 0 G p| ≤ MG)
    (hKvalue : K p = modelCurvature kappa ![p 0, y])
    (hKs : coordPartial 1 K p = coordPartial 1 (modelCurvature kappa) ![p 0, y] / rho)
    (hKt : coordPartial 0 K p = 2 * kappa * p 0 -
      q * coordPartial 1 (modelCurvature kappa) ![p 0, y])
    (hKsmall : |K p| ≤ modelPrincipalRadius g0 kappa rhoMax epsilon R MG ell) :
    modelCoercivityMargin g0 kappa rhoMax epsilon ell / 2 ≤
      directedPrincipal (fun z => G z * K z) ell epsilon p := by
  have hmax : 0 < rhoMax := hrho.trans_le hrhoMax
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have hMG : 0 ≤ MG := (abs_nonneg _).trans hGsi
  have hmodel : |modelCurvature kappa ![p 0, y]| ≤ kappa / 8 := by
    rw [← hKvalue]
    exact hKsmall.trans (min_le_left _ _)
  have hgeo := model_geometric_principal_lower (p := ![p 0, y]) ell hkappa hg0 hG
    hrho hrhoMax heps (by simpa using ht) hq hsmall (by simpa using hy) hmodel
  simp only [Matrix.cons_val_zero] at hgeo
  have hcoeff := modelPrincipal_derivative_remainder_bound ell heps.le heps1 ht hGsi hGti
  have herr : |K p * (-((ell : ℝ) + 1 / 2) * coordPartial 1 G p +
      epsilon * p 0 * coordPartial 0 G p / 2)| ≤
      modelCoercivityMargin g0 kappa rhoMax epsilon ell / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hcoeff (abs_nonneg _)).trans
      (modelPrincipal_radius_error ell hg0 hkappa hmax heps hR hMG hKsmall)
  have heq : directedPrincipal (fun z => G z * K z) ell epsilon p =
      G p * (-(((ell : ℝ) + 1 / 2) / rho + epsilon * p 0 * q / 2) *
        coordPartial 1 (modelCurvature kappa) ![p 0, y] + epsilon * kappa * (p 0) ^ 2) +
      K p * (-((ell : ℝ) + 1 / 2) * coordPartial 1 G p +
        epsilon * p 0 * coordPartial 0 G p / 2) := by
    unfold directedPrincipal
    rw [HessianCalculus.coordPartial_mul_at hGdiff hKdiff 1,
      HessianCalculus.coordPartial_mul_at hGdiff hKdiff 0, hKs, hKt]
    field_simp [hrho.ne']
    ring
  rw [heq]
  linarith [(abs_le.mp herr).1]

end SmoothLocal.Model

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

def capModelCurvature (kappa : ℝ) (Y : ℝ → ℝ → ℝ) : Coord → ℝ :=
  fun p => modelCurvature kappa (capChart Y p)

theorem capChartDomain_isOpen : IsOpen capChartDomain := coordinateRectangle_isOpen _ _ _

theorem capChart_zero (Y : ℝ → ℝ → ℝ) (p : Coord) : capChart Y p 0 = p 0 := by
  simp [capChart, coordinatePoint]

theorem capChart_one (Y : ℝ → ℝ → ℝ) (p : Coord) : capChart Y p 1 = capFlowHeight Y p := by
  simp [capChart, coordinatePoint]

theorem capChart_eq_vec (Y : ℝ → ℝ → ℝ) (p : Coord) :
    capChart Y p = ![p 0, capFlowHeight Y p] := by
  ext i
  fin_cases i <;> simp [capChart_zero, capChart_one]

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

theorem capModelCurvature_contDiffOn (kappa : ℝ)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)) :
    ContDiffOn ℝ ∞ (capModelCurvature kappa Y) capChartDomain :=
  (modelCurvature_contDiff kappa).comp_contDiffOn (capChart_contDiffOn hY)

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

theorem capModelCurvature_partial (kappa : ℝ) {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (i : Fin 2) :
    coordPartial i (capModelCurvature kappa Y) p =
      (if i = 0 then 2 * kappa * p 0 else 0) +
        coordPartial 1 (modelCurvature kappa) (capChart Y p) * coordPartial i (capFlowHeight Y) p := by
  have hheight : DifferentiableAt ℝ (capFlowHeight Y) p :=
    ((capFlowHeight_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hh := ((modelProfile_contDiff.differentiable (by simp) (capFlowHeight Y p)).hasDerivAt).comp_hasFDerivAt
    p hheight.hasFDerivAt
  have hx := hasFDerivAt_apply (𝕜 := ℝ) 0 p
  have hd := ((hx.pow 2).sub hh).const_mul kappa
  simp only [Function.comp_def, Pi.sub_def] at hd
  have hfun : capModelCurvature kappa Y =
      (fun z => kappa * ((z 0) ^ 2 - modelProfile (capFlowHeight Y z))) := by
    funext z
    simp only [capModelCurvature, modelCurvature, capChart_zero, capChart_one]
  rw [hfun, modelCurvature_partial]
  simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, capChart_one, coordPartial]
  rw [hd.fderiv]
  fin_cases i <;> simp <;> ring

theorem capModelCurvature_partial_time (kappa : ℝ) {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hp : p ∈ capChartDomain) :
    coordPartial 0 (capModelCurvature kappa Y) p = 2 * kappa * p 0 -
      q (capChart Y p) * coordPartial 1 (modelCurvature kappa) (capChart Y p) := by
  rw [capModelCurvature_partial kappa hY hp 0, capFlowHeight_partial_time hY hode hp]
  norm_num only [↓reduceIte, if_true]
  ring

theorem capModelCurvature_partial_initial (kappa : ℝ) {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) :
    coordPartial 1 (capModelCurvature kappa Y) p =
      coordPartial 1 (modelCurvature kappa) (capChart Y p) / capChartRho Y p := by
  rw [capModelCurvature_partial kappa hY hp 1]
  simp [capChartRho, div_eq_mul_inv]

theorem capChart_mem_modelSquare {p : Coord} (hp : p ∈ capChartDomain)
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) :
    capChart Y p ∈ modelSquare := by
  apply coordinatePoint_mem_modelSquare
  · exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
  · have hd := abs_le.mp hdisp
    exact ⟨by linarith [hp.2.1, hd.1], by linarith [hp.2.2, hd.2]⟩

theorem cap_model_full_principal_lower
    {G : Coord → ℝ} {p : Coord} {kappa g0 rhoMax epsilon MG : ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hdisp : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      |Y s t - s| ≤ (1 : ℝ) / 50)
    (hqsmall : ∀ z ∈ modelSquare, |q z| ≤ (1 : ℝ) / 100)
    (hp : p ∈ capChartDomain) (hs : p 1 ≤ 0) (ell : ℕ)
    (hGdiff : DifferentiableAt ℝ G p) (hkappa : 0 < kappa) (hg0 : 0 < g0)
    (hG : g0 ≤ G p) (hrhoMax : capChartRho Y p ≤ rhoMax)
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hsmall : epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hGsi : |coordPartial 1 G p| ≤ MG) (hGti : |coordPartial 0 G p| ≤ MG)
    (hKsmall : |capModelCurvature kappa Y p| ≤
      modelPrincipalRadius g0 kappa rhoMax epsilon 2 MG ell) :
    modelCoercivityMargin g0 kappa rhoMax epsilon ell / 2 ≤
      directedPrincipal (fun z => G z * capModelCurvature kappa Y z) ell epsilon p := by
  have hdispP : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50 :=
    hdisp (p 1) ⟨hp.2.1.le, hp.2.2.le⟩ (p 0) ⟨hp.1.1.le, hp.1.2.le⟩
  have hy : capFlowHeight Y p ≤ 1 / 50 := by linarith [(abs_le.mp hdispP).2]
  have hKdiff : DifferentiableAt ℝ (capModelCurvature kappa Y) p :=
    ((capModelCurvature_contDiffOn kappa hY).contDiffAt
      (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hKvalue : capModelCurvature kappa Y p =
      modelCurvature kappa ![p 0, capFlowHeight Y p] := by
    unfold capModelCurvature
    rw [capChart_eq_vec]
  have hKs : coordPartial 1 (capModelCurvature kappa Y) p =
      coordPartial 1 (modelCurvature kappa) ![p 0, capFlowHeight Y p] / capChartRho Y p := by
    rw [capModelCurvature_partial_initial kappa hY hp, capChart_eq_vec]
  have hKt : coordPartial 0 (capModelCurvature kappa Y) p =
      2 * kappa * p 0 - q (capChart Y p) *
        coordPartial 1 (modelCurvature kappa) ![p 0, capFlowHeight Y p] := by
    rw [capModelCurvature_partial_time kappa hY hode hp]
    rw [capChart_eq_vec]
  exact model_full_principal_lower ell hGdiff hKdiff hkappa hg0 hG
    (capChartRho_pos hY hvar hp) hrhoMax heps heps1 (abs_lt.mpr hp.1).le
    (hqsmall _ (capChart_mem_modelSquare hp hdispP)) hsmall hy hGsi hGti hKvalue hKs hKt hKsmall

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
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

variable {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord}
variable {Y : ℝ → ℝ → ℝ} {p : Coord} {kappa : ℝ}

theorem patch_capCurvature_eventually_model
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (hk : 0 < kappa) (hU : IsOpen U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (himage : capChart Y p ∈ U)
    (hsmall : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤ kappa / 8) :
    capPullback Y (gaussianCurvature (g0 + eta)) =ᶠ[𝓝 p] capModelCurvature kappa Y := by
  have heq := patch_smallCurvature_eventually_model hk hU hbackground hsupport hcentral himage hsmall
  have hc : ContinuousAt (capChart Y) p :=
    (capChart_contDiffOn hY).continuousOn.continuousAt (capChartDomain_isOpen.mem_nhds hp)
  exact heq.comp_tendsto hc.tendsto

theorem patch_heightChartA_eventually_model
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (hk : 0 < kappa) (hU : IsOpen U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (himage : capChart Y p ∈ U)
    (hsmall : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤ kappa / 8) :
    heightChartA (g0 + eta) z Y =ᶠ[𝓝 p]
      (fun q => heightChartG1 (g0 + eta) z Y q * capModelCurvature kappa Y q) := by
  have heq := patch_capCurvature_eventually_model hY hp hk hU hbackground hsupport hcentral himage hsmall
  filter_upwards [heq] with q hq
  rw [heightChartA_eq, hq]

theorem patch_heightChart_near_principal_lower
    (hg : SmoothPositiveOn (g0 + eta) U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian (g0 + eta) z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient (g0 + eta) z (coordinatePoint t (Y s t)))
        (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hdisp : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      |Y s t - s| ≤ (1 : ℝ) / 50)
    (hqsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0 + eta) z p| ≤ (1 : ℝ) / 100)
    (hmap : MapsTo (capChart Y) capChartDomain U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (hp : p ∈ capChartDomain) (hs : p 1 ≤ 0) (ell : ℕ)
    {cG rhoMax epsilon MG : ℝ}
    (hkappa : 0 < kappa) (hcG : 0 < cG) (hG : cG ≤ heightChartG1 (g0 + eta) z Y p)
    (hrhoMax : capChartRho Y p ≤ rhoMax) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hsmall : epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hGs : |coordPartial 1 (heightChartG1 (g0 + eta) z Y) p| ≤ MG)
    (hGt : |coordPartial 0 (heightChartG1 (g0 + eta) z Y) p| ≤ MG)
    (hKsmall : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤
      modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell) :
    modelCoercivityMargin cG kappa rhoMax epsilon ell / 2 ≤
      directedPrincipal (heightChartA (g0 + eta) z Y) ell epsilon p := by
  have hK8 := hKsmall.trans (min_le_left _ _)
  have hKeq := patch_capCurvature_eventually_model hY hp hkappa hU hbackground hsupport hcentral
    (hmap hp) hK8
  have hAeq := patch_heightChartA_eventually_model (z := z) hY hp hkappa hU hbackground hsupport hcentral
    (hmap hp) hK8
  have hGsm : ContDiffOn ℝ ∞ (heightChartG1 (g0 + eta) z Y) capChartDomain :=
    (capPullback_contDiffOn hY (darbouxG_contDiffOn hg hU hz hyy) hmap).mul
      ((capChartRho_contDiffOn hY hvar).pow 2)
  have hGdiff := (hGsm.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hKmodel : |capModelCurvature kappa Y p| ≤
      modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell := by
    rw [← hKeq.self_of_nhds]
    exact hKsmall
  have hmodel := cap_model_full_principal_lower hY hode hvar hdisp hqsmall hp hs ell hGdiff
    hkappa hcG hG hrhoMax heps heps1 hsmall hGs hGt hKmodel
  have hprincipal : directedPrincipal (heightChartA (g0 + eta) z Y) ell epsilon p =
      directedPrincipal (fun q => heightChartG1 (g0 + eta) z Y q * capModelCurvature kappa Y q)
        ell epsilon p := by
    unfold directedPrincipal
    rw [coordPartial_eq_of_eventuallyEq hAeq 1, coordPartial_eq_of_eventuallyEq hAeq 0]
  rw [hprincipal]
  exact hmodel

theorem actual_positive_curvature_strip_budget
    {G K d D c1 lambda M mu : ℝ}
    (hd : 0 < d) (hD : d ≤ D) (hc1 : 0 ≤ c1) (hlambda : 0 ≤ lambda)
    (hG : 0 ≤ G) (hGM : G ≤ M) (hK : K ≤ c1 * d)
    (hbudget : M * c1 * (lambda * D + 8) ≤ mu / 3) :
    (lambda + 8 / d) * (G * K) ≤ mu / 3 := by
  have hM : 0 ≤ M := hG.trans hGM
  have hH : 0 ≤ lambda + 8 / d := add_nonneg hlambda (div_nonneg (by norm_num) hd.le)
  have hGK : G * K ≤ M * (c1 * d) :=
    (mul_le_mul_of_nonneg_left hK hG).trans
      (mul_le_mul_of_nonneg_right hGM (mul_nonneg hc1 hd.le))
  calc
    _ ≤ (lambda + 8 / d) * (M * (c1 * d)) := mul_le_mul_of_nonneg_left hGK hH
    _ = M * c1 * (lambda * d + 8) := by field_simp [hd.ne']
    _ ≤ M * c1 * (lambda * D + 8) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hD hlambda) le_rfl) (mul_nonneg hM hc1)
    _ ≤ mu / 3 := hbudget

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

theorem patch_actual_directed_near_coercivity
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord}
    {Y : ℝ → ℝ → ℝ} {p : Coord} {kappa : ℝ}
    (hg : SmoothPositiveOn (g0 + eta) U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hDarboux : ∀ p ∈ U,
      (covHessian (g0 + eta) z p).det = gaussianCurvature (g0 + eta) p * heightEnergy (g0 + eta) z p)
    (hyy : ∀ p ∈ U, covHessian (g0 + eta) z p 1 1 ≠ 0)
    (hE : ∀ p ∈ U, 0 < heightEnergy (g0 + eta) z p)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient (g0 + eta) z (coordinatePoint t (Y s t)))
        (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hdisp : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      |Y s t - s| ≤ (1 : ℝ) / 50)
    (hqsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0 + eta) z p| ≤ (1 : ℝ) / 100)
    (hmap : MapsTo (capChart Y) capChartDomain U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (hp : p ∈ capChartDomain) (hs : p 1 ≤ 0) (ell : ℕ)
    (cG rhoMax epsilon MG MI MB Mr MA MAs MG1 c1 D edge lambda : ℝ)
    (hkappa : 0 < kappa) (hcG : 0 < cG) (hG : cG ≤ heightChartG1 (g0 + eta) z Y p)
    (hrhoMax : capChartRho Y p ≤ rhoMax) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hqbudget : epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hGs : |coordPartial 1 (heightChartG1 (g0 + eta) z Y) p| ≤ MG)
    (hGt : |coordPartial 0 (heightChartG1 (g0 + eta) z Y) p| ≤ MG)
    (hKsmall : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤
      modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell)
    (hedge : p 1 < edge) (hlambda : 0 < lambda)
    (hIs : |coordPartial 1 (coordinatePrimitive (heightChartB (g0 + eta) z Y ell)) p| ≤ MI)
    (hBp : |heightChartB (g0 + eta) z Y ell p| ≤ MB)
    (hr : |heightChartRemainder (g0 + eta) z Y ell p| ≤ Mr)
    (hAp : |heightChartA (g0 + eta) z Y p| ≤ MA)
    (hAs : |coordPartial 1 (heightChartA (g0 + eta) z Y) p| ≤ MAs)
    (hTbudget : 2 * (MI + epsilon + epsilon * 2 * MB) ≤ lambda)
    (hEbudget : (MI + 1 + 2 * MB) / 2 + Mr ≤ lambda / 8)
    (hcrossbudget : 4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 *
      epsilon^2 * MA ≤ 1 / 8)
    (hloss : (4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 * epsilon^2) / lambda ≤
      modelCoercivityMargin cG kappa rhoMax epsilon ell / 8)
    (hGmax : heightChartG1 (g0 + eta) z Y p ≤ MG1)
    (hc1 : 0 ≤ c1) (hdist : edge - p 1 ≤ D)
    (hKstrip : capPullback Y (gaussianCurvature (g0 + eta)) p ≤ c1 * (edge - p 1))
    (hstripbudget : MG1 * c1 * (lambda * D + 8) ≤
      modelCoercivityMargin cG kappa rhoMax epsilon ell / 6)
    (x y : ℝ) :
    let A := heightChartA (g0 + eta) z Y
    let B := heightChartB (g0 + eta) z Y ell
    let C := heightChartC (g0 + eta) z Y ell
    let I := coordinatePrimitive B
    min (lambda / 8) (modelCoercivityMargin cG kappa rhoMax epsilon ell / 4) *
      directedWeight edge lambda I p * (x^2 + y^2) ≤
      multiplierT B (directedM edge lambda I) (directedN edge lambda epsilon I) p * x^2 +
        multiplierS A C (directedM edge lambda I) (directedN edge lambda epsilon I) p * y^2 +
        multiplierJ A B C (directedM edge lambda I) (directedN edge lambda epsilon I) p * x * y := by
  let mu := modelCoercivityMargin cG kappa rhoMax epsilon ell / 2
  have hmu : 0 < mu := div_pos
    (modelCoercivityMargin_pos ell hcG hkappa ((capChartRho_pos hY hvar hp).trans_le hrhoMax) heps)
    (by norm_num)
  have hA : DifferentiableAt ℝ (heightChartA (g0 + eta) z Y) p :=
    ((heightChartA_contDiffOn hg hU hz hyy hY hvar hmap).contDiffAt
      (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hB : ContDiffOn ℝ ∞ (heightChartB (g0 + eta) z Y ell) (coordinateRectangle 2 (-2) 2) :=
    heightChartB_contDiffOn hg hU hz hyy hY hmap ell
  have hC := heightChartC_factor hg hU hz hDarboux hyy hE hY hvar hmap hp ell
  have hprincipal : mu ≤ directedPrincipal (heightChartA (g0 + eta) z Y) ell epsilon p :=
    patch_heightChart_near_principal_lower hg hU hz hyy hY hode hvar hdisp hqsmall hmap
      hbackground hsupport hcentral hp hs ell hkappa hcG hG hrhoMax heps heps1 hqbudget hGs hGt hKsmall
  have hstrip : 0 < heightChartA (g0 + eta) z Y p →
      weightH0 edge lambda p * heightChartA (g0 + eta) z Y p ≤ mu / 3 := by
    intro hpositive
    rw [heightChartA_eq]
    apply actual_positive_curvature_strip_budget (sub_pos.mpr hedge) hdist hc1 hlambda.le
      (hcG.trans_le hG).le hGmax hKstrip
    dsimp only [mu]
    linarith
  have hloss' : (4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 * epsilon^2) / lambda ≤
      mu / 4 := by dsimp only [mu]; linarith
  have hh := primitive_directed_near_coercivity hB (by norm_num : (0 : ℝ) < 2) hp
    (heightChartA (g0 + eta) z Y) (heightChartC (g0 + eta) z Y ell)
    (heightChartRemainder (g0 + eta) z Y ell) hA edge lambda epsilon ell hedge hlambda
    heps.le heps1 hC MI MB Mr MA MAs mu hmu hIs hBp hr hAp hAs hTbudget hEbudget hcrossbudget
    hloss' hprincipal hstrip x y
  have hm : mu / 2 = modelCoercivityMargin cG kappa rhoMax epsilon ell / 4 := by
    dsimp only [mu]
    ring
  rw [hm] at hh
  exact hh

end SmoothLocal.Flow

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Flow.patch_actual_directed_near_coercivity := @OAI.SmoothLocal.Flow.patch_actual_directed_near_coercivity
