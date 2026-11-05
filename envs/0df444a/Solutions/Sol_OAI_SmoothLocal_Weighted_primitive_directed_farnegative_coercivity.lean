-- Prove2me | solution 1 for OAI.SmoothLocal.Weighted.primitive_directed_farnegative_coercivity
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:31:23.287141+00:00
-- url     : https://prove2.me/submissions/91aa3d3d-a74b-497d-bef6-5c7108d7416f

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
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace HessianCalculus

variable {f h : Coord → ℝ} {p : Coord}

theorem coordPartial_mul_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q * h q) p =
      coordPartial i f p * h p + f p * coordPartial i h p := by
  simp [coordPartial, fderiv_fun_mul hf hh, add_comm, mul_comm]

end HessianCalculus

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

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

theorem normalized_negative_far_coercivity {H A MA L mu Q e E alpha Pmax : ℝ}
    (hH : 0 < H) (hL : 0 ≤ L) (hmu : 0 < mu) (hA : A ≤ 0) (hAM : |A| ≤ MA)
    (hsmall : L * MA ≤ 1 / 8) (hloss : L / H ≤ mu / 4)
    (he : |e| ≤ E) (hEH : E ≤ H / 8) (hQ : -Pmax ≤ Q)
    (halpha : alpha ≤ |A|) (hbudget : Pmax + mu ≤ H * alpha / 4) :
    mu / 2 ≤ Q - H * A / 2 + A * e - L * (H⁻¹ + H * A ^ 2) := by
  have hcross := normalized_loss_budget hH hL hAM hsmall hloss
  have herr := residual_abs_error_bound (A := A) he hEH
  have hmargin : Pmax + mu ≤ H * |A| / 4 := by
    have hm := mul_le_mul_of_nonneg_left halpha hH.le
    nlinarith
  rw [abs_of_nonpos hA] at *
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

theorem directedPrincipal_abs_bound {A : Coord → ℝ} {p : Coord}
    (ell : ℕ) {epsilon R MAs MAt : ℝ} (heps : 0 ≤ epsilon)
    (ht : |p 0| ≤ R) (hAs : |coordPartial 1 A p| ≤ MAs)
    (hAt : |coordPartial 0 A p| ≤ MAt) :
    |directedPrincipal A ell epsilon p| ≤ directedPrincipalBound ell epsilon R MAs MAt := by
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have hMAt : 0 ≤ MAt := (abs_nonneg _).trans hAt
  have hbeta : 0 ≤ (ell : ℝ) + 1 / 2 := by positivity
  have hfirst : |-((ell : ℝ) + 1 / 2) * coordPartial 1 A p| ≤ ((ell : ℝ) + 1 / 2) * MAs := by
    rw [abs_mul, abs_neg, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left hAs hbeta
  have hsecond : |epsilon * p 0 * coordPartial 0 A p / 2| ≤ epsilon * R * MAt / 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg heps, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left ht heps) hAt (abs_nonneg _) (mul_nonneg heps hR))
      (by norm_num)
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

theorem primitive_directed_farnegative_coercivity
    {B : Coord → ℝ} {R a b : ℝ} {p : Coord}
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (A C r : Coord → ℝ)
    (hA : DifferentiableAt ℝ A p) (edge lambda epsilon : ℝ) (ell : ℕ)
    (hedge : p 1 < edge) (hlambda : 0 < lambda)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hC : C p = ((ell : ℝ) + 1) * coordPartial 1 A p + A p * r p)
    (MI MB Mr MA MAs MAt mu alpha : ℝ) (hmu : 0 < mu)
    (hIs : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI)
    (hBp : |B p| ≤ MB) (hr : |r p| ≤ Mr)
    (hAp : |A p| ≤ MA) (hAs : |coordPartial 1 A p| ≤ MAs)
    (hTbudget : 2 * (MI + epsilon + epsilon * R * MB) ≤ lambda)
    (hEbudget : (MI + 1 + R * MB) / 2 + Mr ≤ lambda / 8)
    (hsmall : 4 * (R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)) ^ 2 *
      epsilon ^ 2 * MA ≤ 1 / 8)
    (hloss : (4 * (R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)) ^ 2 *
      epsilon ^ 2) / lambda ≤ mu / 4)
    (hAt : |coordPartial 0 A p| ≤ MAt)
    (halpha : 0 < alpha) (hAfar : A p ≤ -alpha)
    (hdominance : directedPrincipalBound ell epsilon R MAs MAt + mu ≤ lambda * alpha / 4)
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
    convert hm using 1 <;> try with_reducible_and_instances rfl
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
    have hn : A p ≤ 0 := hAfar.trans (by linarith)
    have hAa : alpha ≤ |A p| := by rw [abs_of_nonpos hn]; linarith
    have hprincipal : -directedPrincipalBound ell epsilon R MAs MAt ≤
        directedPrincipal A ell epsilon p :=
      (abs_le.mp (directedPrincipal_abs_bound ell heps (abs_lt.mpr hp.1).le hAs hAt)).1
    have hbudget : directedPrincipalBound ell epsilon R MAs MAt + mu ≤ H * alpha / 4 :=
      hdominance.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hlH halpha.le) (by norm_num))
    exact normalized_negative_far_coercivity hH hL hmu hn hAp hsmall hLH he hEH
      hprincipal hAa hbudget
  exact actual_quadratic_coercivity hW hH hlambda hmu hlH hT
    (primitive_directedS_expansion hB hR hp A C r hA edge lambda epsilon ell hedge hC)
    hcross hmargin

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted

end SmoothLocal.Flow

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Weighted.primitive_directed_farnegative_coercivity := @OAI.SmoothLocal.Weighted.primitive_directed_farnegative_coercivity
