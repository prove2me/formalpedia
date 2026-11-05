-- Prove2me | solution 1 for OAI.SmoothLocal.Flow.capFlowHeight_coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:34:18.132164+00:00
-- url     : https://prove2.me/submissions/daa68349-df27-4c7d-aac0-bf55531a0706

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

variable {Y : ℝ → ℝ → ℝ}

theorem capFlowHeight_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)) :
    ContDiffOn ℝ ∞ (capFlowHeight Y) capChartDomain := by
  exact hY.comp ((contDiffOn_apply ℝ ℝ 0 _).prodMk (contDiffOn_apply ℝ ℝ 1 _))
    (fun p hp => hp)

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

theorem flowCoordinateMap_mem_modelSquare {p : ℝ × ℝ}
    (hp : p ∈ pairRectangle 2 (-2) 2) : flowCoordinateMap Y p ∈ modelSquare := by
  have hF := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hbound : Y p.2 p.1 ∈ Icc (-3 : ℝ) 3 := by
    apply isClosed_Icc.mem_of_tendsto
      (hF.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).continuousAt
    filter_upwards [(pairRectangle_isOpen 2 (-2) 2).mem_nhds hp] with point hpoint
    exact hrange point.2 ⟨hpoint.2.1.le, hpoint.2.2.le⟩
      point.1 ⟨hpoint.1.1.le, hpoint.1.2.le⟩
  exact coordinatePoint_mem_modelSquare ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
    hbound

theorem flowPullback_contDiffOn {C : Coord → ℝ} (hC : ContDiffOn ℝ ∞ C U) :
    ContDiffOn ℝ ∞ (fun p => C (flowCoordinateMap Y p)) (pairRectangle 2 (-2) 2) := by
  have hF := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hT : ContDiffOn ℝ ∞ (flowCoordinateMap Y) (pairRectangle 2 (-2) 2) :=
    (contDiffOn_fst.smul contDiffOn_const).add (hF.smul contDiffOn_const)
  exact hC.comp hT (fun p hp => hSU
    (flowCoordinateMap_mem_modelSquare hq hU hSU hY hrange hstart hode hp))

theorem initialFlowDerivative_eq_pairPartialY {p : ℝ × ℝ}
    (hp : p ∈ pairRectangle 2 (-2) 2) :
    initialFlowDerivative Y p = pairPartialY (fun v : ℝ × ℝ => Y v.2 v.1) p := by
  have hF := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hd := ((hF.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt
  exact (hd.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

theorem initialFlowDerivative_contDiffOn :
    ContDiffOn ℝ ∞ (initialFlowDerivative Y) (pairRectangle 2 (-2) 2) := by
  have hF := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hd : ContDiffOn ℝ ∞ (pairPartialY (fun v : ℝ × ℝ => Y v.2 v.1))
      (pairRectangle 2 (-2) 2) :=
    (hF.fderiv_of_isOpen (pairRectangle_isOpen 2 (-2) 2) (by simp)).clm_apply contDiffOn_const
  exact hd.congr (fun p hp => initialFlowDerivative_eq_pairPartialY
    hq hU hSU hY hrange hstart hode hp)

theorem flowPullback_partial_y {C : Coord → ℝ} (hC : ContDiffOn ℝ ∞ C U)
    {p : ℝ × ℝ} (hp : p ∈ pairRectangle 2 (-2) 2) :
    pairPartialY (fun v => C (flowCoordinateMap Y v)) p =
      coordPartial 1 C (flowCoordinateMap Y p) * initialFlowDerivative Y p := by
  have hsY : HasDerivAt (fun s => Y s p.1) (initialFlowDerivative Y p) p.2 :=
    (cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hp.2 hp.1).differentiableAt.hasDerivAt
  have hsT : HasDerivAt (fun s => flowCoordinateMap Y (p.1, s))
      (initialFlowDerivative Y p • Pi.single 1 (1 : ℝ)) p.2 := by
    convert
      ((hasDerivAt_const p.2 p.1).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add
        (hsY.smul_const (Pi.single 1 (1 : ℝ) : Coord)) using 1 <;>
      first | rfl | simp
  have hmem := hSU (flowCoordinateMap_mem_modelSquare hq hU hSU hY hrange hstart hode hp)
  have hdC := ((hC.contDiffAt (hU.mem_nhds hmem)).differentiableAt (by simp)).hasFDerivAt
  have hchain : HasDerivAt (fun s => C (flowCoordinateMap Y (p.1, s)))
      (coordPartial 1 C (flowCoordinateMap Y p) * initialFlowDerivative Y p) p.2 := by
    convert hdC.comp_hasDerivAt p.2 hsT using 1 <;>
      first | rfl | simp only [map_smul, smul_eq_mul, coordPartial, mul_comm]
  have hB := flowPullback_contDiffOn hq hU hSU hY hrange hstart hode hC
  have hdB : HasFDerivAt (fun v : ℝ × ℝ => C (flowCoordinateMap Y v))
      (fderiv ℝ (fun v : ℝ × ℝ => C (flowCoordinateMap Y v)) p) p :=
    ((hB.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).differentiableAt
      (by simp)).hasFDerivAt
  have hpair : HasDerivAt (fun s => C (flowCoordinateMap Y (p.1, s)))
      (pairPartialY (fun v => C (flowCoordinateMap Y v)) p) p.2 := by
    convert hdB.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)) using 1 <;> rfl
  exact hpair.unique hchain

theorem cap_flow_initial_second_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => deriv (fun v => Y v t) u)
      (-deriv (fun v => Y v t) s *
        (∫ r in 0..t, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
          deriv (fun v => Y v r) s)) s := by
  let B (p : ℝ × ℝ) := coordPartial 1 q (flowCoordinateMap Y p)
  have hB : ContDiffOn ℝ ∞ B (pairRectangle 2 (-2) 2) :=
    flowPullback_contDiffOn hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 1)
  have hI := pairPrimitive_hasDerivAt_y (hB.of_le (by simp)) ht hs
  have hdiag : pairPrimitive (pairPartialY B) (t, s) =
      ∫ r in 0..t, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
        deriv (fun v => Y v r) s := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Ioo (-2 : ℝ) 2 := by
      have hz : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := by norm_num
      exact ⟨(lt_min hz.1 ht.1).trans_le hr.1, hr.2.trans_lt (max_lt hz.2 ht.2)⟩
    exact flowPullback_partial_y hq hU hSU hY hrange hstart hode
      (partial_contDiffOn hq hU 1) ⟨hr', hs⟩
  have hV : HasDerivAt (fun u => Real.exp (-pairPrimitive B (t, u)))
      (Real.exp (-pairPrimitive B (t, s)) * -pairPrimitive (pairPartialY B) (t, s)) s := hI.neg.exp
  have he : (fun u => deriv (fun v => Y v t) u) =ᶠ[𝓝 s]
      (fun u => Real.exp (-pairPrimitive B (t, u))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact (cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hu ht).deriv
  have hVs : Real.exp (-pairPrimitive B (t, s)) = deriv (fun v => Y v t) s :=
    (cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hs ht).deriv.symm
  rw [hdiag, hVs] at hV
  convert hV.congr_of_eventuallyEq he using 1 <;> try with_reducible_and_instances rfl
  first | rfl | ring

theorem cap_flow_initial_second_formula {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    deriv (fun u => deriv (fun v => Y v t) u) s =
      -deriv (fun v => Y v t) s *
        (∫ r in 0..t, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
          deriv (fun v => Y v r) s) :=
  (cap_flow_initial_second_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

theorem flow_initial_second_integral_bound {M : ℝ} (hM : 0 ≤ M)
    (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hMqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    IntervalIntegrable (fun r => coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
      deriv (fun v => Y v r) s) volume 0 t ∧
    |∫ r in 0..t, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
      deriv (fun v => Y v r) s| ≤ 2 * M * Real.exp (2 * M) := by
  let C (p : ℝ × ℝ) := coordPartial 1 (coordPartial 1 q) (flowCoordinateMap Y p) * initialFlowDerivative Y p
  have hC : ContDiffOn ℝ ∞ C (pairRectangle 2 (-2) 2) :=
    (flowPullback_contDiffOn hq hU hSU hY hrange hstart hode
      (partial_contDiffOn (partial_contDiffOn hq hU 1) hU 1)).mul
      (initialFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode)
  have hc : ContinuousOn (fun r => C (r, s)) (Ioo (-2 : ℝ) 2) :=
    hC.continuousOn.comp (f := fun r => (r, s)) (by fun_prop) (fun r hr => ⟨hr, hs⟩)
  have hseg : uIcc (0 : ℝ) t ⊆ Ioo (-2 : ℝ) 2 := by
    intro r hr
    have hz : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := by norm_num
    exact ⟨(lt_min hz.1 ht.1).trans_le hr.1, hr.2.trans_lt (max_lt hz.2 ht.2)⟩
  refine ⟨(hc.mono hseg).intervalIntegrable, ?_⟩
  have hbound (r : ℝ) (hr : r ∈ uIcc (0 : ℝ) t) :
      ‖coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) * deriv (fun v => Y v r) s‖ ≤
        M * Real.exp (2 * M) := by
    have hr' := hseg hr
    have hys := cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hs hr'
    have hpos := cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs hr'
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
    exact mul_le_mul (hMqq _ (flowCoordinateMap_mem_modelSquare (p := (r, s)) hq hU hSU hY hrange hstart hode
      ⟨hr', hs⟩)) hys.2 hpos.le hM
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (C := M * Real.exp (2 * M))
    (fun r hr => hbound r (uIoc_subset_uIcc hr))
  have ht2 : |t| ≤ 2 := (abs_lt.mpr ht).le
  calc
    _ ≤ (M * Real.exp (2 * M)) * |t| := by simpa only [Real.norm_eq_abs, sub_zero] using hi
    _ ≤ (M * Real.exp (2 * M)) * 2 := mul_le_mul_of_nonneg_left ht2
      (mul_nonneg hM (Real.exp_pos _).le)
    _ = 2 * M * Real.exp (2 * M) := by ring

theorem cap_flow_initial_second_bound {M : ℝ} (hM : 0 ≤ M)
    (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hMqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => deriv (fun v => Y v t) u) s| ≤ 2 * M * Real.exp (4 * M) := by
  rw [cap_flow_initial_second_formula hq hU hSU hY hrange hstart hode hs ht, abs_mul,
    abs_neg, abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht)]
  calc
    _ ≤ Real.exp (2 * M) * (2 * M * Real.exp (2 * M)) :=
      mul_le_mul (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hs ht).2
        (flow_initial_second_integral_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hs ht).2
        (abs_nonneg _) (Real.exp_pos _).le
    _ = (2 * M) * (Real.exp (2 * M) * Real.exp (2 * M)) := by ring
    _ = 2 * M * Real.exp (4 * M) := by
      rw [← Real.exp_add]
      congr 2
      ring

end ActualFlow
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

def initialSecondFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun u => deriv (fun v => Y v p.1) u) p.2

def initialSecondForcing (q : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ r in 0..p.1, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y p.2 r)) *
    deriv (fun v => Y v r) p.2

def initialThirdForcing (q : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ r in 0..p.1,
    coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (coordinatePoint r (Y p.2 r)) *
      (deriv (fun v => Y v r) p.2) ^ 2 +
    coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y p.2 r)) *
      deriv (fun u => deriv (fun v => Y v r) u) p.2

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

theorem flowPullback_hasDerivAt_y {C : Coord → ℝ} (hC : ContDiffOn ℝ ∞ C U)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => C (coordinatePoint t (Y u t)))
      (coordPartial 1 C (coordinatePoint t (Y s t)) * deriv (fun u => Y u t) s) s := by
  have hB := flowPullback_contDiffOn hq hU hSU hY hrange hstart hode hC
  have hd : HasFDerivAt (fun p : ℝ × ℝ => C (flowCoordinateMap Y p))
      (fderiv ℝ (fun p : ℝ × ℝ => C (flowCoordinateMap Y p)) (t, s)) (t, s) :=
    ((hB.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds ⟨ht, hs⟩)).differentiableAt
      (by simp)).hasFDerivAt
  have hh := hd.comp_hasDerivAt s ((hasDerivAt_const s t).prodMk (hasDerivAt_id s))
  change HasDerivAt (fun u => C (coordinatePoint t (Y u t)))
    (pairPartialY (fun p => C (flowCoordinateMap Y p)) (t, s)) s at hh
  rw [flowPullback_partial_y hq hU hSU hY hrange hstart hode hC ⟨ht, hs⟩] at hh
  exact hh

theorem initialSecondFlowDerivative_contDiffOn :
    ContDiffOn ℝ ∞ (initialSecondFlowDerivative Y) (pairRectangle 2 (-2) 2) := by
  have hV := initialFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode
  have hd : ContDiffOn ℝ ∞ (pairPartialY (initialFlowDerivative Y))
      (pairRectangle 2 (-2) 2) :=
    (hV.fderiv_of_isOpen (pairRectangle_isOpen 2 (-2) 2) (by simp)).clm_apply contDiffOn_const
  apply hd.congr
  intro p hp
  have hder := ((hV.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt
  exact (hder.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

theorem initialSecondForcing_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => initialSecondForcing q Y (t, u))
      (initialThirdForcing q Y (t, s)) s := by
  let C (p : ℝ × ℝ) := coordPartial 1 (coordPartial 1 q) (flowCoordinateMap Y p) *
    initialFlowDerivative Y p
  have hqq := partial_contDiffOn (partial_contDiffOn hq hU 1) hU 1
  have hC : ContDiffOn ℝ ∞ C (pairRectangle 2 (-2) 2) :=
    (flowPullback_contDiffOn hq hU hSU hY hrange hstart hode hqq).mul
      (initialFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode)
  have hi := pairPrimitive_hasDerivAt_y (hC.of_le (by simp)) ht hs
  have heq : pairPrimitive (pairPartialY C) (t, s) = initialThirdForcing q Y (t, s) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hz : (0 : ℝ) ∈ Ioo (-2) 2 := by norm_num
    have hr' : r ∈ Ioo (-2 : ℝ) 2 :=
      ⟨(lt_min hz.1 ht.1).trans_le hr.1, hr.2.trans_lt (max_lt hz.2 ht.2)⟩
    have hqder := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode hqq hs hr'
    have hVder := (cap_flow_initial_second_hasDerivAt hq hU hSU hY hrange hstart hode hs hr').differentiableAt.hasDerivAt
    have hprod := hqder.mul hVder
    have hfd : HasFDerivAt C (fderiv ℝ C (r, s)) (r, s) :=
      ((hC.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds ⟨hr', hs⟩)).differentiableAt
        (by simp)).hasFDerivAt
    have he := (hfd.comp_hasDerivAt s
      ((hasDerivAt_const s r).prodMk (hasDerivAt_id s))).unique hprod
    change pairPartialY C (r, s) = _ at he
    change pairPartialY C (r, s) = _
    rw [he]
    ring
  rw [heq] at hi
  exact hi

theorem cap_flow_initial_third_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => initialSecondFlowDerivative Y (t, u))
      (-initialSecondFlowDerivative Y (t, s) * initialSecondForcing q Y (t, s) -
        initialFlowDerivative Y (t, s) * initialThirdForcing q Y (t, s)) s := by
  have hV : HasDerivAt (fun u => initialFlowDerivative Y (t, u))
      (initialSecondFlowDerivative Y (t, s)) s :=
    (cap_flow_initial_second_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).differentiableAt.hasDerivAt
  have hI := initialSecondForcing_hasDerivAt hq hU hSU hY hrange hstart hode hs ht
  have hproduct : HasDerivAt
      (fun u => -initialFlowDerivative Y (t, u) * initialSecondForcing q Y (t, u))
      (-initialSecondFlowDerivative Y (t, s) * initialSecondForcing q Y (t, s) +
        -initialFlowDerivative Y (t, s) * initialThirdForcing q Y (t, s)) s := hV.neg.mul hI
  have he : (fun u => initialSecondFlowDerivative Y (t, u)) =ᶠ[𝓝 s]
      (fun u => -initialFlowDerivative Y (t, u) * initialSecondForcing q Y (t, u)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact cap_flow_initial_second_formula hq hU hSU hY hrange hstart hode hu ht
  convert hproduct.congr_of_eventuallyEq he using 1 <;> try with_reducible_and_instances rfl
  first | rfl | ring

theorem cap_flow_initial_third_formula {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    deriv (fun u => initialSecondFlowDerivative Y (t, u)) s =
      -initialSecondFlowDerivative Y (t, s) * initialSecondForcing q Y (t, s) -
        initialFlowDerivative Y (t, s) * initialThirdForcing q Y (t, s) :=
  (cap_flow_initial_third_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

theorem initialThirdForcing_integrable_bound {M : ℝ} (hM : 0 ≤ M)
    (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hMqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 q) p| ≤ M)
    (hMqqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 (coordPartial 1 q)) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    IntervalIntegrable (fun r =>
      coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (coordinatePoint r (Y s r)) *
        (deriv (fun v => Y v r) s)^2 +
      coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
        deriv (fun u => deriv (fun v => Y v r) u) s) volume 0 t ∧
    |initialThirdForcing q Y (t, s)| ≤ (2 * M + 4 * M^2) * Real.exp (4 * M) := by
  let C (p : ℝ × ℝ) :=
    coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (flowCoordinateMap Y p) * (initialFlowDerivative Y p)^2 +
    coordPartial 1 (coordPartial 1 q) (flowCoordinateMap Y p) * initialSecondFlowDerivative Y p
  have hqq := partial_contDiffOn (partial_contDiffOn hq hU 1) hU 1
  have hC : ContDiffOn ℝ ∞ C (pairRectangle 2 (-2) 2) :=
    ((flowPullback_contDiffOn hq hU hSU hY hrange hstart hode (partial_contDiffOn hqq hU 1)).mul
      ((initialFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode).pow 2)).add
      ((flowPullback_contDiffOn hq hU hSU hY hrange hstart hode hqq).mul
        (initialSecondFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode))
  have hc : ContinuousOn (fun r => C (r, s)) (Ioo (-2 : ℝ) 2) :=
    hC.continuousOn.comp (f := fun r => (r, s)) (by fun_prop) (fun r hr => ⟨hr, hs⟩)
  have hseg : uIcc (0 : ℝ) t ⊆ Ioo (-2 : ℝ) 2 := by
    intro r hr
    have hz : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := by norm_num
    exact ⟨(lt_min hz.1 ht.1).trans_le hr.1, hr.2.trans_lt (max_lt hz.2 ht.2)⟩
  refine ⟨(hc.mono hseg).intervalIntegrable, ?_⟩
  have hbound (r : ℝ) (hr : r ∈ uIcc (0 : ℝ) t) :
      ‖C (r, s)‖ ≤ (M + 2 * M^2) * Real.exp (4 * M) := by
    have hr' := hseg hr
    have hp := flowCoordinateMap_mem_modelSquare (p := (r, s)) hq hU hSU hY hrange hstart hode ⟨hr', hs⟩
    have hV := (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hs hr').2
    have hVpos := cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs hr'
    have hVsq : |(deriv (fun v => Y v r) s)^2| ≤ Real.exp (4 * M) := by
      rw [abs_of_nonneg (sq_nonneg _)]
      calc
        _ ≤ (Real.exp (2 * M))^2 := pow_le_pow_left₀ hVpos.le hV 2
        _ = Real.exp (4 * M) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
    have hW := cap_flow_initial_second_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hs hr'
    rw [Real.norm_eq_abs]
    calc
      |C (r, s)| ≤
          |coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (coordinatePoint r (Y s r))| *
            |(deriv (fun v => Y v r) s)^2| +
          |coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r))| *
            |deriv (fun u => deriv (fun v => Y v r) u) s| := by
        calc
          _ ≤ |coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (coordinatePoint r (Y s r)) *
              (deriv (fun v => Y v r) s)^2| +
              |coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
                deriv (fun u => deriv (fun v => Y v r) u) s| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ M * Real.exp (4 * M) + M * (2 * M * Real.exp (4 * M)) :=
        add_le_add (mul_le_mul (hMqqq _ hp) hVsq (abs_nonneg _) hM)
          (mul_le_mul (hMqq _ hp) hW (abs_nonneg _) hM)
      _ = (M + 2 * M^2) * Real.exp (4 * M) := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (C := (M + 2 * M^2) * Real.exp (4 * M)) (f := fun r => C (r, s))
    (fun r hr => hbound r (uIoc_subset_uIcc hr))
  have ht2 : |t| ≤ 2 := (abs_lt.mpr ht).le
  calc
    _ ≤ ((M + 2 * M^2) * Real.exp (4 * M)) * |t| := by
      simpa only [Real.norm_eq_abs, sub_zero, initialThirdForcing, C,
        flowCoordinateMap, initialFlowDerivative, initialSecondFlowDerivative] using hi
    _ ≤ ((M + 2 * M^2) * Real.exp (4 * M)) * 2 := mul_le_mul_of_nonneg_left ht2
      (mul_nonneg (by positivity) (Real.exp_pos _).le)
    _ = (2 * M + 4 * M^2) * Real.exp (4 * M) := by ring

theorem cap_flow_initial_third_bound {M : ℝ} (hM : 0 ≤ M)
    (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hMqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 q) p| ≤ M)
    (hMqqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 (coordPartial 1 q)) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => initialSecondFlowDerivative Y (t, u)) s| ≤
      (2 * M + 8 * M^2) * Real.exp (6 * M) := by
  rw [cap_flow_initial_third_formula hq hU hSU hY hrange hstart hode hs ht]
  have hW := cap_flow_initial_second_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hs ht
  have hI := (flow_initial_second_integral_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hs ht).2
  have hJ := (initialThirdForcing_integrable_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hMqqq hs ht).2
  have hV : |initialFlowDerivative Y (t, s)| ≤ Real.exp (2 * M) := by
    unfold initialFlowDerivative
    rw [abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht)]
    exact (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hs ht).2
  calc
    _ ≤ |initialSecondFlowDerivative Y (t, s)| * |initialSecondForcing q Y (t, s)| +
        |initialFlowDerivative Y (t, s)| * |initialThirdForcing q Y (t, s)| := by
      simpa only [abs_mul, abs_neg] using
        abs_sub (-(initialSecondFlowDerivative Y (t, s)) * initialSecondForcing q Y (t, s))
          (initialFlowDerivative Y (t, s) * initialThirdForcing q Y (t, s))
    _ ≤ (2 * M * Real.exp (4 * M)) * (2 * M * Real.exp (2 * M)) +
        Real.exp (2 * M) * ((2 * M + 4 * M^2) * Real.exp (4 * M)) :=
      add_le_add (mul_le_mul hW hI (abs_nonneg _) (by positivity))
        (mul_le_mul hV hJ (abs_nonneg _) (Real.exp_pos _).le)
    _ = (2 * M + 8 * M^2) * (Real.exp (2 * M) * Real.exp (4 * M)) := by ring
    _ = (2 * M + 8 * M^2) * Real.exp (6 * M) := by
      rw [← Real.exp_add]
      congr 2
      ring

end ActualFlow
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

def timeFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (Y p.2) p.1

def timeSecondFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun u => deriv (Y p.2) u) p.1

def mixedFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun u => timeFlowDerivative Y (p.1, u)) p.2

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

theorem cap_flow_time_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (Y s) (-q (coordinatePoint t (Y s t))) t := by
  have hsmooth := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have htime : DifferentiableAt ℝ (Y s) t :=
    ((hsmooth.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds ⟨ht, hs⟩)).differentiableAt
      (by simp)).comp t (differentiableAt_id.prodMk (differentiableAt_const s))
  have hderiv := (hode s ⟨hs.1.le, hs.2.le⟩ t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  simpa only [hderiv.deriv] using htime.hasDerivAt

theorem timeFlowDerivative_eq {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    timeFlowDerivative Y (t, s) = -q (coordinatePoint t (Y s t)) :=
  (cap_flow_time_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

theorem flowPullback_hasDerivAt_t {C : Coord → ℝ} (hC : ContDiffOn ℝ ∞ C U)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => C (coordinatePoint u (Y s u)))
      (coordPartial 0 C (coordinatePoint t (Y s t)) -
        q (coordinatePoint t (Y s t)) * coordPartial 1 C (coordinatePoint t (Y s t))) t := by
  have hT : HasDerivAt (fun u => coordinatePoint u (Y s u))
      (Pi.single 0 (1 : ℝ) - q (coordinatePoint t (Y s t)) • Pi.single 1 (1 : ℝ) : Coord) t := by
    convert
      ((hasDerivAt_id t).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add
        ((cap_flow_time_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).smul_const
          (Pi.single 1 (1 : ℝ) : Coord)) using 1 <;>
      first | rfl | simp only [coordinatePoint, one_smul, neg_smul, sub_eq_add_neg]
  have hp := hSU (flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩)
  have hC' := ((hC.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  convert hC'.comp_hasDerivAt t hT using 1 <;>
    first | rfl | simp only [map_sub, map_smul, smul_eq_mul, coordPartial, flowCoordinateMap]

theorem cap_flow_mixed_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => timeFlowDerivative Y (t, u))
      (-coordPartial 1 q (coordinatePoint t (Y s t)) * initialFlowDerivative Y (t, s)) s := by
  have hd := (flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode hq hs ht).neg
  have he : (fun u => timeFlowDerivative Y (t, u)) =ᶠ[𝓝 s]
      (fun u => -q (coordinatePoint t (Y u t))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact timeFlowDerivative_eq hq hU hSU hY hrange hstart hode hu ht
  convert hd.congr_of_eventuallyEq he using 1 <;> try with_reducible_and_instances rfl
  first | rfl | (dsimp [initialFlowDerivative]; ring)

theorem mixedFlowDerivative_eq {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    mixedFlowDerivative Y (t, s) =
      -coordPartial 1 q (coordinatePoint t (Y s t)) * initialFlowDerivative Y (t, s) :=
  (cap_flow_mixed_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

theorem cap_flow_time_second_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => timeFlowDerivative Y (u, s))
      (-coordPartial 0 q (coordinatePoint t (Y s t)) +
        coordPartial 1 q (coordinatePoint t (Y s t)) * q (coordinatePoint t (Y s t))) t := by
  have hd := (flowPullback_hasDerivAt_t hq hU hSU hY hrange hstart hode hq hs ht).neg
  have he : (fun u => timeFlowDerivative Y (u, s)) =ᶠ[𝓝 t]
      (fun u => -q (coordinatePoint u (Y s u))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact timeFlowDerivative_eq hq hU hSU hY hrange hstart hode hs hu
  convert hd.congr_of_eventuallyEq he using 1 <;> try with_reducible_and_instances rfl
  first | rfl | ring

theorem timeSecondFlowDerivative_eq {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    timeSecondFlowDerivative Y (t, s) =
      -coordPartial 0 q (coordinatePoint t (Y s t)) +
        coordPartial 1 q (coordinatePoint t (Y s t)) * q (coordinatePoint t (Y s t)) :=
  (cap_flow_time_second_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

theorem cap_flow_mixed_initial_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => mixedFlowDerivative Y (t, u))
      (-coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t)) *
          (initialFlowDerivative Y (t, s))^2 -
        coordPartial 1 q (coordinatePoint t (Y s t)) * initialSecondFlowDerivative Y (t, s)) s := by
  have hdq := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 1) hs ht
  have hdV : HasDerivAt (fun u => initialFlowDerivative Y (t, u))
      (initialSecondFlowDerivative Y (t, s)) s :=
    (cap_flow_initial_second_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).differentiableAt.hasDerivAt
  have hd := hdq.neg.mul hdV
  have he : (fun u => mixedFlowDerivative Y (t, u)) =ᶠ[𝓝 s]
      (fun u => -coordPartial 1 q (coordinatePoint t (Y u t)) * initialFlowDerivative Y (t, u)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact mixedFlowDerivative_eq hq hU hSU hY hrange hstart hode hu ht
  convert hd.congr_of_eventuallyEq he using 1 <;> try with_reducible_and_instances rfl
  first | rfl | (dsimp [initialFlowDerivative]; ring)

theorem cap_flow_time_second_initial_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => timeSecondFlowDerivative Y (t, u))
      ((-coordPartial 1 (coordPartial 0 q) (coordinatePoint t (Y s t)) +
        coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t)) * q (coordinatePoint t (Y s t)) +
        (coordPartial 1 q (coordinatePoint t (Y s t)))^2) * initialFlowDerivative Y (t, s)) s := by
  have hd0 := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 0) hs ht
  have hd1 := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 1) hs ht
  have hdq := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode hq hs ht
  have hd := hd0.neg.add (hd1.mul hdq)
  have he : (fun u => timeSecondFlowDerivative Y (t, u)) =ᶠ[𝓝 s]
      (fun u => -coordPartial 0 q (coordinatePoint t (Y u t)) +
        coordPartial 1 q (coordinatePoint t (Y u t)) * q (coordinatePoint t (Y u t))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact timeSecondFlowDerivative_eq hq hU hSU hY hrange hstart hode hu ht
  convert hd.congr_of_eventuallyEq he using 1 <;> try with_reducible_and_instances rfl
  first | rfl | (dsimp [initialFlowDerivative]; ring)

theorem cap_flow_time_third_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => timeSecondFlowDerivative Y (u, s))
      (-coordPartial 0 (coordPartial 0 q) (coordinatePoint t (Y s t)) +
        q (coordinatePoint t (Y s t)) * coordPartial 1 (coordPartial 0 q) (coordinatePoint t (Y s t)) +
        (coordPartial 0 (coordPartial 1 q) (coordinatePoint t (Y s t)) -
          q (coordinatePoint t (Y s t)) * coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t))) *
          q (coordinatePoint t (Y s t)) +
        coordPartial 1 q (coordinatePoint t (Y s t)) *
          (coordPartial 0 q (coordinatePoint t (Y s t)) -
            q (coordinatePoint t (Y s t)) * coordPartial 1 q (coordinatePoint t (Y s t)))) t := by
  have hd0 := flowPullback_hasDerivAt_t hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 0) hs ht
  have hd1 := flowPullback_hasDerivAt_t hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 1) hs ht
  have hdq := flowPullback_hasDerivAt_t hq hU hSU hY hrange hstart hode hq hs ht
  have hd := hd0.neg.add (hd1.mul hdq)
  have he : (fun u => timeSecondFlowDerivative Y (u, s)) =ᶠ[𝓝 t]
      (fun u => -coordPartial 0 q (coordinatePoint u (Y s u)) +
        coordPartial 1 q (coordinatePoint u (Y s u)) * q (coordinatePoint u (Y s u))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact timeSecondFlowDerivative_eq hq hU hSU hY hrange hstart hode hs hu
  convert hd.congr_of_eventuallyEq he using 1 <;> try with_reducible_and_instances rfl
  first | rfl | ring

end ActualFlow
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

theorem abs_transport_bound {a b c M : ℝ} (hM : 0 ≤ M)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ 1) :
    |a - c * b| ≤ 2 * M := by
  calc
    _ ≤ |a| + |c| * |b| := by simpa only [abs_mul] using abs_sub a (c * b)
    _ ≤ M + 1 * M := add_le_add ha (by
      simpa only [mul_comm] using mul_le_mul hb hc (abs_nonneg _) hM)
    _ = 2 * M := by ring

theorem abs_second_initial_coefficient_bound {a b c d M : ℝ} (hM : 0 ≤ M)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ 1) (hd : |d| ≤ M) :
    |-a + b * c + d^2| ≤ 2 * M + M^2 := by
  have hbase : |-a + b * c| ≤ 2 * M := by
    calc
      _ = |-(a - c * b)| := by congr 1; ring
      _ = |a - c * b| := abs_neg _
      _ ≤ 2 * M := abs_transport_bound hM ha hb hc
  have hsq : |d^2| ≤ M^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  exact (abs_add_le _ _).trans (add_le_add hbase hsq)

theorem abs_third_time_coefficient_bound {a00 a10 a01 a11 a0 a1 c M : ℝ}
    (hM : 0 ≤ M) (hc : |c| ≤ 1)
    (h00 : |a00| ≤ M) (h10 : |a10| ≤ M) (h01 : |a01| ≤ M)
    (h11 : |a11| ≤ M) (h0 : |a0| ≤ M) (h1 : |a1| ≤ M) :
    |-a00 + c * a10 + (a01 - c * a11) * c + a1 * (a0 - c * a1)| ≤
      4 * M + 2 * M^2 := by
  have ha : |-a00 + c * a10| ≤ 2 * M := by
    calc
      _ = |-(a00 - c * a10)| := by congr 1; ring
      _ = |a00 - c * a10| := abs_neg _
      _ ≤ 2 * M := abs_transport_bound hM h00 h10 hc
  have hb := abs_transport_bound hM h01 h11 hc
  have hd := abs_transport_bound hM h0 h1 hc
  calc
    _ ≤ |-a00 + c * a10| + |a01 - c * a11| * |c| + |a1| * |a0 - c * a1| := by
      simpa only [abs_mul] using (abs_add_le (-a00 + c * a10 + (a01 - c * a11) * c)
        (a1 * (a0 - c * a1))).trans
          (add_le_add (abs_add_le (-a00 + c * a10) ((a01 - c * a11) * c)) le_rfl)
    _ ≤ 2 * M + (2 * M) * 1 + M * (2 * M) :=
      add_le_add (add_le_add ha (mul_le_mul hb hc (abs_nonneg _) (by positivity)))
        (mul_le_mul h1 hd (abs_nonneg _) hM)
    _ = 4 * M + 2 * M^2 := by ring

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

theorem cap_flow_time_bound
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |timeFlowDerivative Y (t, s)| ≤ (1 : ℝ) / 100 := by
  rw [timeFlowDerivative_eq hq hU hSU hY hrange hstart hode hs ht, abs_neg]
  exact hq0 _ (flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩)

theorem cap_flow_time_second_bound {M : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ 1)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |timeSecondFlowDerivative Y (t, s)| ≤ 2 * M := by
  rw [timeSecondFlowDerivative_eq hq hU hSU hY hrange hstart hode hs ht]
  have hp := flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩
  have hh := abs_transport_bound hM (hq1 0 _ hp) (hq1 1 _ hp) (hq0 _ hp)
  calc
    _ = |-(coordPartial 0 q (coordinatePoint t (Y s t)) -
        q (coordinatePoint t (Y s t)) * coordPartial 1 q (coordinatePoint t (Y s t)))| := by
      congr 1; ring
    _ = |coordPartial 0 q (coordinatePoint t (Y s t)) -
        q (coordinatePoint t (Y s t)) * coordPartial 1 q (coordinatePoint t (Y s t))| := abs_neg _
    _ ≤ 2 * M := hh

theorem cap_flow_mixed_bound {M : ℝ} (hM : 0 ≤ M)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |mixedFlowDerivative Y (t, s)| ≤ M * Real.exp (2 * M) := by
  rw [mixedFlowDerivative_eq hq hU hSU hY hrange hstart hode hs ht, abs_mul, abs_neg, initialFlowDerivative,
    abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht)]
  exact mul_le_mul (hq1 1 _
    (flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩))
    (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hs ht).2
    (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht).le hM

theorem cap_flow_mixed_initial_bound {M : ℝ} (hM : 0 ≤ M)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => mixedFlowDerivative Y (t, u)) s| ≤
      (M + 2 * M^2) * Real.exp (4 * M) := by
  rw [(cap_flow_mixed_initial_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv]
  have hp := flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩
  have hV := (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hs ht).2
  have hVpos := cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht
  have hVsq : |(initialFlowDerivative Y (t, s))^2| ≤ Real.exp (4 * M) := by
    rw [abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (Real.exp (2 * M))^2 := pow_le_pow_left₀ hVpos.le hV 2
      _ = Real.exp (4 * M) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hW := cap_flow_initial_second_bound hq hU hSU hY hrange hstart hode hM (hq1 1) (hq2 1 1) hs ht
  calc
    _ ≤ |coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t))| *
        |(initialFlowDerivative Y (t, s))^2| +
        |coordPartial 1 q (coordinatePoint t (Y s t))| * |initialSecondFlowDerivative Y (t, s)| := by
      calc
        _ ≤ |-coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t)) *
            (initialFlowDerivative Y (t, s))^2| +
            |coordPartial 1 q (coordinatePoint t (Y s t)) * initialSecondFlowDerivative Y (t, s)| :=
          abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_neg]
    _ ≤ M * Real.exp (4 * M) + M * (2 * M * Real.exp (4 * M)) :=
      add_le_add (mul_le_mul (hq2 1 1 _ hp) hVsq (abs_nonneg _) hM)
        (mul_le_mul (hq1 1 _ hp) hW (abs_nonneg _) hM)
    _ = (M + 2 * M^2) * Real.exp (4 * M) := by ring

theorem cap_flow_time_second_initial_bound {M : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ 1)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => timeSecondFlowDerivative Y (t, u)) s| ≤
      (2 * M + M^2) * Real.exp (2 * M) := by
  rw [(cap_flow_time_second_initial_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv,
    abs_mul, initialFlowDerivative, abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht)]
  have hp := flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩
  exact mul_le_mul
    (abs_second_initial_coefficient_bound hM (hq2 1 0 _ hp) (hq2 1 1 _ hp) (hq0 _ hp) (hq1 1 _ hp))
    (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hs ht).2
    (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht).le (by positivity)

theorem cap_flow_time_third_bound {M : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ 1)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => timeSecondFlowDerivative Y (u, s)) t| ≤ 4 * M + 2 * M^2 := by
  rw [(cap_flow_time_third_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv]
  have hp := flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩
  exact abs_third_time_coefficient_bound hM (hq0 _ hp)
    (hq2 0 0 _ hp) (hq2 1 0 _ hp) (hq2 0 1 _ hp) (hq2 1 1 _ hp)
    (hq1 0 _ hp) (hq1 1 _ hp)

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

theorem coordPartial_time_of_pair_eq {f : Coord → ℝ} {F : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f capChartDomain)
    (he : ∀ p ∈ capChartDomain, f p = F (p 0, p 1))
    {p : Coord} (hp : p ∈ capChartDomain) :
    coordPartial 0 f p = deriv (fun t => F (t, p 1)) (p 0) := by
  have hd := ((hf.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hp' : boxPoint (p 0) (p 1) = p := boxPoint_coord_eta p
  have hd' : HasFDerivAt f (fderiv ℝ f p) (boxPoint (p 0) (p 1)) := by rw [hp']; exact hd
  have hline := hd'.comp_hasDerivAt (p 0) (boxPoint_hasDerivAt_t (p 0) (p 1))
  have hevent : (fun t => F (t, p 1)) =ᶠ[𝓝 (p 0)] (fun t => f (boxPoint t (p 1))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.1] with t ht
    have hm : boxPoint t (p 1) ∈ capChartDomain := by
      simpa [capChartDomain, coordinateRectangle, boxPoint] using And.intro ht hp.2
    simpa [boxPoint] using (he (boxPoint t (p 1)) hm).symm
  exact (hline.congr_of_eventuallyEq hevent).deriv.symm

theorem coordPartial_initial_of_pair_eq {f : Coord → ℝ} {F : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f capChartDomain)
    (he : ∀ p ∈ capChartDomain, f p = F (p 0, p 1))
    {p : Coord} (hp : p ∈ capChartDomain) :
    coordPartial 1 f p = deriv (fun s => F (p 0, s)) (p 1) := by
  have hd := ((hf.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hp' : boxPoint (p 0) (p 1) = p := boxPoint_coord_eta p
  have hd' : HasFDerivAt f (fderiv ℝ f p) (boxPoint (p 0) (p 1)) := by rw [hp']; exact hd
  have hline := hd'.comp_hasDerivAt (p 1) (boxPoint_hasDerivAt_s (p 0) (p 1))
  have hevent : (fun s => F (p 0, s)) =ᶠ[𝓝 (p 1)] (fun s => f (boxPoint (p 0) s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.2] with s hs
    have hm : boxPoint (p 0) s ∈ capChartDomain := by
      simpa [capChartDomain, coordinateRectangle, boxPoint] using And.intro hp.1 hs
    simpa [boxPoint] using (he (boxPoint (p 0) s) hm).symm
  exact (hline.congr_of_eventuallyEq hevent).deriv.symm

section HeightWords
variable {Y : ℝ → ℝ → ℝ}
variable (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
include hY

theorem capFlowHeight_partial_zero_eq {p : Coord} (hp : p ∈ capChartDomain) :
    coordPartial 0 (capFlowHeight Y) p = timeFlowDerivative Y (p 0, p 1) :=
  (capFlowHeight_hasDerivAt_time hY hp).deriv.symm

theorem capFlowHeight_partial_one_eq {p : Coord} (hp : p ∈ capChartDomain) :
    coordPartial 1 (capFlowHeight Y) p = initialFlowDerivative Y (p 0, p 1) :=
  (capFlowHeight_hasDerivAt_initial hY hp).deriv.symm

theorem capFlowHeight_word_00 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [0, 0] (capFlowHeight Y) p = timeSecondFlowDerivative Y (p 0, p 1) :=
  coordPartial_time_of_pair_eq
    (partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 0)
    (fun _ hx => capFlowHeight_partial_zero_eq hY hx) hp

theorem capFlowHeight_word_10 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 0] (capFlowHeight Y) p = mixedFlowDerivative Y (p 0, p 1) :=
  coordPartial_initial_of_pair_eq
    (partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 0)
    (fun _ hx => capFlowHeight_partial_zero_eq hY hx) hp

theorem capFlowHeight_word_11 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 1] (capFlowHeight Y) p = initialSecondFlowDerivative Y (p 0, p 1) :=
  coordPartial_initial_of_pair_eq
    (partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1)
    (fun _ hx => capFlowHeight_partial_one_eq hY hx) hp

theorem capFlowHeight_word_000 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [0, 0, 0] (capFlowHeight Y) p =
      deriv (fun t => timeSecondFlowDerivative Y (t, p 1)) (p 0) :=
  coordPartial_time_of_pair_eq
    (LowQuotient.iterated_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen [0, 0])
    (fun _ hx => capFlowHeight_word_00 hY hx) hp

theorem capFlowHeight_word_100 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 0, 0] (capFlowHeight Y) p =
      deriv (fun s => timeSecondFlowDerivative Y (p 0, s)) (p 1) :=
  coordPartial_initial_of_pair_eq
    (LowQuotient.iterated_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen [0, 0])
    (fun _ hx => capFlowHeight_word_00 hY hx) hp

theorem capFlowHeight_word_110 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 1, 0] (capFlowHeight Y) p =
      deriv (fun s => mixedFlowDerivative Y (p 0, s)) (p 1) :=
  coordPartial_initial_of_pair_eq
    (LowQuotient.iterated_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen [1, 0])
    (fun _ hx => capFlowHeight_word_10 hY hx) hp

theorem capFlowHeight_word_111 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 1, 1] (capFlowHeight Y) p =
      deriv (fun s => initialSecondFlowDerivative Y (p 0, s)) (p 1) :=
  coordPartial_initial_of_pair_eq
    (LowQuotient.iterated_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen [1, 1])
    (fun _ hx => capFlowHeight_word_11 hY hx) hp

end HeightWords

theorem iterated_three_swap_outer {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (i j k : Fin 2) :
    iteratedCoordPartial [i, j, k] f p = iteratedCoordPartial [j, i, k] f p :=
  coordPartial_comm (partial_contDiffOn hf hU k) hU hp i j

theorem iterated_three_swap_inner {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (i j k : Fin 2) :
    iteratedCoordPartial [i, j, k] f p = iteratedCoordPartial [i, k, j] f p := by
  have he : coordPartial j (coordPartial k f) =ᶠ[𝓝 p] coordPartial k (coordPartial j f) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact coordPartial_comm hf hU hx j k
  exact coordPartial_eq_of_eventuallyEq he i

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

omit hq2 hq3 in
theorem capFlowHeight_word_one_bound
    (_ : ∀ first second : Fin 2, ∀ point ∈ modelSquare,
      |coordPartial first (coordPartial second q) point| ≤ M)
    (_ : ∀ first second third : Fin 2, ∀ point ∈ modelSquare,
      |coordPartial first (coordPartial second (coordPartial third q)) point| ≤ M)
    {p : Coord} (hp : p ∈ capChartDomain) (i : Fin 2) :
    |iteratedCoordPartial [i] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  obtain ⟨_, h1, hV, _⟩ := flowCoordinateBound_dominates hM
  fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one]
  · rw [show iteratedCoordPartial [0] (capFlowHeight Y) p = timeFlowDerivative Y (p 0, p 1) from
      capFlowHeight_partial_zero_eq hs hp]
    exact (cap_flow_time_bound hq hU hSU hY hrange hstart hode hq0 hp.2 hp.1).trans
      ((by norm_num : (1 : ℝ) / 100 ≤ 1).trans h1)
  · rw [show iteratedCoordPartial [1] (capFlowHeight Y) p = initialFlowDerivative Y (p 0, p 1) from
      capFlowHeight_partial_one_eq hs hp, initialFlowDerivative,
      abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hp.2 hp.1)]
    exact (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hp.2 hp.1).2.trans hV

omit hq3 in
theorem capFlowHeight_word_two_bound
    (_ : ∀ first second third : Fin 2, ∀ point ∈ modelSquare,
      |coordPartial first (coordPartial second (coordPartial third q)) point| ≤ M)
    {p : Coord} (hp : p ∈ capChartDomain) (i j : Fin 2) :
    |iteratedCoordPartial [i, j] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hf := capFlowHeight_contDiffOn hs
  obtain ⟨_, _, _, htt, hts, hss, _⟩ := flowCoordinateBound_dominates hM
  have hqweak (p : Coord) (hp : p ∈ modelSquare) : |q p| ≤ 1 :=
    (hq0 p hp).trans (by norm_num)
  have h00 : |iteratedCoordPartial [0, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_00 hs hp]
    exact (cap_flow_time_second_bound hq hU hSU hY hrange hstart hode hM hqweak hq1 hp.2 hp.1).trans htt
  have h10 : |iteratedCoordPartial [1, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_10 hs hp]
    exact (cap_flow_mixed_bound hq hU hSU hY hrange hstart hode hM hq1 hp.2 hp.1).trans hts
  have h11 : |iteratedCoordPartial [1, 1] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_11 hs hp]
    exact (cap_flow_initial_second_bound hq hU hSU hY hrange hstart hode hM (hq1 1) (hq2 1 1) hp.2 hp.1).trans hss
  fin_cases i <;> fin_cases j <;> simp only [Fin.mk_zero, Fin.mk_one]
  · exact h00
  · have he : iteratedCoordPartial [0, 1] (capFlowHeight Y) p = iteratedCoordPartial [1, 0] (capFlowHeight Y) p :=
      coordPartial_comm hf capChartDomain_isOpen hp 0 1
    rw [he]; exact h10
  · exact h10
  · exact h11

theorem capFlowHeight_word_three_bound {p : Coord} (hp : p ∈ capChartDomain) (i j k : Fin 2) :
    |iteratedCoordPartial [i, j, k] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hf := capFlowHeight_contDiffOn hs
  obtain ⟨_, _, _, _, _, _, httt, htts, htss, hsss⟩ := flowCoordinateBound_dominates hM
  have hqweak (p : Coord) (hp : p ∈ modelSquare) : |q p| ≤ 1 :=
    (hq0 p hp).trans (by norm_num)
  have h000 : |iteratedCoordPartial [0, 0, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_000 hs hp]
    exact (cap_flow_time_third_bound hq hU hSU hY hrange hstart hode hM hqweak hq1 hq2 hp.2 hp.1).trans httt
  have h100 : |iteratedCoordPartial [1, 0, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_100 hs hp]
    exact (cap_flow_time_second_initial_bound hq hU hSU hY hrange hstart hode hM hqweak hq1 hq2 hp.2 hp.1).trans htts
  have h110 : |iteratedCoordPartial [1, 1, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_110 hs hp]
    exact (cap_flow_mixed_initial_bound hq hU hSU hY hrange hstart hode hM hq1 hq2 hp.2 hp.1).trans htss
  have h111 : |iteratedCoordPartial [1, 1, 1] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_111 hs hp]
    exact (cap_flow_initial_third_bound hq hU hSU hY hrange hstart hode hM (hq1 1) (hq2 1 1) (hq3 1 1 1) hp.2 hp.1).trans hsss
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp only [Fin.mk_zero, Fin.mk_one]
  · exact h000
  · rw [iterated_three_swap_inner hf capChartDomain_isOpen hp 0 0 1,
      iterated_three_swap_outer hf capChartDomain_isOpen hp 0 1 0]
    exact h100
  · rw [iterated_three_swap_outer hf capChartDomain_isOpen hp 0 1 0]
    exact h100
  · rw [iterated_three_swap_outer hf capChartDomain_isOpen hp 0 1 1,
      iterated_three_swap_inner hf capChartDomain_isOpen hp 1 0 1]
    exact h110
  · exact h100
  · rw [iterated_three_swap_inner hf capChartDomain_isOpen hp 1 0 1]
    exact h110
  · exact h110
  · exact h111

theorem capFlowHeight_coordinate_bound :
    CoordinateBound (capFlowHeight Y) capChartDomain 3 (flowCoordinateBound M) := by
  intro ds hds p hp
  cases ds with
  | nil =>
    have hh : |capFlowHeight Y p| ≤ 3 := abs_le.mpr
      (hrange (p 1) ⟨hp.2.1.le, hp.2.2.le⟩ (p 0) ⟨hp.1.1.le, hp.1.2.le⟩)
    exact hh.trans (flowCoordinateBound_dominates hM).1
  | cons i ds =>
    cases ds with
    | nil => exact capFlowHeight_word_one_bound hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3 hp i
    | cons j ds =>
      cases ds with
      | nil => exact capFlowHeight_word_two_bound hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3 hp i j
      | cons k ds =>
        cases ds with
        | nil => exact capFlowHeight_word_three_bound hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3 hp i j k
        | cons l ds => simp only [List.length_cons] at hds; omega

end ActualFlow
end SmoothLocal.Flow

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Flow.capFlowHeight_coordinate_bound := @OAI.SmoothLocal.Flow.capFlowHeight_coordinate_bound
