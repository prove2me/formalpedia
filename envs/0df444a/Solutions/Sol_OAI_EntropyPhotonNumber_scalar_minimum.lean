-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.scalar_minimum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:31:45.757464+00:00
-- url     : https://prove2.me/submissions/9accf1e9-9605-46e3-ae8a-388c0fe3c885

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Interpolation.lean:L504-L539
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.scalar_minimum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Theorems.Thm_OAI_EntropyPhotonNumber_genericAdditionalE_pos

-- ---- from OAI.InformationTheory.PhotonNumber.Functions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber

open Set Filter Topology

theorem b_pos (x : ℝ) : 0 < b x := mul_pos (f_pos x) (Real.cosh_pos x)

theorem f_mul_sinh (x : ℝ) : f x * Real.sinh x = x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [f_of_ne_zero hx, div_mul_cancel₀ _ (Real.sinh_ne_zero.mpr hx)]

theorem b_sq (x : ℝ) : b x ^ 2 = f x ^ 2 + x ^ 2 := by
  have h := Real.cosh_sq_sub_sinh_sq x
  have hx := f_mul_sinh x
  dsimp [b]
  nlinarith [sq_nonneg (f x), sq_nonneg (Real.sinh x),
    congrArg (fun t : ℝ => t ^ 2) hx]

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric

namespace EntropyPhotonNumber

open Set Filter Topology
theorem target_mul_add (x y : ℝ) :
    (f x * f y / f (x + y)) * (x + y) = y * b x + x * b y := by
  calc
    (f x * f y / f (x + y)) * (x + y) =
      (f x * f y / f (x + y)) * (f (x + y) * Real.sinh (x + y)) := by
        congr 1
        exact (f_mul_sinh (x + y)).symm
    _ = f x * f y * Real.sinh (x + y) := by
      rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt (f_pos (x + y)))]
    _ = f x * f y * (Real.sinh x * Real.cosh y + Real.cosh x * Real.sinh y) := by
      rw [Real.sinh_add]
    _ =
      f y * (f x * Real.sinh x) * Real.cosh y +
      (f y * Real.sinh y) * (f x * Real.cosh x) := by ring
    _ = y * b x + x * b y := by
      rw [f_mul_sinh, f_mul_sinh]
      dsimp [b]
      ring

theorem target_eq_of_add_ne_zero {x y : ℝ} (hxy : x + y ≠ 0) :
    f x * f y / f (x + y) = (y * b x + x * b y) / (x + y) := by
  exact (eq_div_iff hxy).mpr (target_mul_add x y)

theorem continuous_b : Continuous b := continuous_f.mul Real.continuous_cosh

end EntropyPhotonNumber

end

end OAI

-- ---- from OAI.Analysis.DiagonalForms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace DiagonalForms.System
end DiagonalForms.System

namespace QuantumCalculus
end QuantumCalculus

namespace DiagonalForms.System
end DiagonalForms.System

namespace DiagonalForms.System
open EntropyPhotonNumber

end DiagonalForms.System

end

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace DiagonalForms

namespace System

variable {P I J : Type*} (D : System P I J)

end System

end DiagonalForms

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

section CompactIntegral
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

end CompactIntegral
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
theorem integral_unitInterval (f : ℝ → ℝ) :
    (∫ t : UnitInterval, f t.val) = ∫ t in (0 : ℝ)..1, f t := by
  rw [integral_subtype measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num)]

theorem affine_pos {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (t : UnitInterval) :
    0 < (1 - t.val) * X + t.val * Y := by
  rcases t.property.1.eq_or_lt with ht | ht
  · simp [← ht, hX]
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr t.property.2) hX.le) (mul_pos ht hY)
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

end DiagonalForms.System

namespace DiagonalForms.System
open Function
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

end

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Interpolation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal

namespace EntropyPhotonNumber
open Herglotz MeasureTheory

end EntropyPhotonNumber

namespace EntropyPhotonNumber.Herglotz

end EntropyPhotonNumber.Herglotz

namespace EntropyPhotonNumber
open MeasureTheory Herglotz

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace EntropyPhotonNumber

section
open DiagonalForms.System MeasureTheory Set Filter Topology

theorem genericAdditionalE_difference {B₀ D : ℝ → ℝ}
    (hc : ContinuousOn D (Ioi 0)) (hp : ∀ q, 0 < q → 0 < D q)
    (hd : ∀ q, 0 < q → HasDerivAt B₀ (-D q/2) q)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    2*genericAdditionalE D s t*(B₀ s-B₀ t) = t-s := by
  have hpos := genericAdditionalE_pos hc hp hs ht
  let q (θ : ℝ) := (1-θ)*s+θ*t
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hqp (θ : ℝ) (hθ : θ ∈ Icc 0 1) : 0 < q θ := affine_pos hs ht ⟨θ, hθ⟩
  have hI : IntervalIntegrable (fun θ => -D (q θ)/2*(t-s)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((hc.comp hqc.continuousOn hqp).neg.div_const 2).mul_const (t-s)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ => B₀ (q θ)) (f' := fun θ => -D (q θ)/2*(t-s)) (a := 0) (b := 1) (by
      intro θ hθ
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hθ
      have hq : HasDerivAt q (t-s) θ := by
        convert! (((hasDerivAt_const θ 1).sub (hasDerivAt_id θ)).mul_const s).add
          ((hasDerivAt_id θ).mul_const t) using 1
        ring
      exact (hd _ (hqp θ hθ)).comp θ hq) hI
  have hei : (∫ θ : UnitInterval, D (q θ.val)) = ∫ θ in (0 : ℝ)..1, D (q θ) :=
    by convert! integral_unitInterval (fun θ => D (q θ)) using 1
  have hnorm : (t-s)*(∫ θ : UnitInterval, D (q θ.val)) = 2*(B₀ s-B₀ t) := by
    rw [hei]
    have hq0 : q 0 = s := by simp [q]
    have hq1 : q 1 = t := by simp [q]
    rw [hq0, hq1] at hFTC
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
      intervalIntegral.integral_neg] at hFTC
    nlinarith
  have hn : (∫ θ : UnitInterval, D (q θ.val)) ≠ 0 := by
    exact (mt inv_eq_zero.mpr) (ne_of_gt hpos)
  dsimp [genericAdditionalE]
  calc
    2 * (∫ θ : UnitInterval, D ((1-θ.val)*s+θ.val*t))⁻¹ * (B₀ s-B₀ t) =
        (2*(B₀ s-B₀ t))*(∫ θ : UnitInterval, D (q θ.val))⁻¹ := by ring
    _ = t-s := by rw [← hnorm, mul_inv_cancel_right₀ hn]

theorem continuous_genericAdditionalE_f {D : ℝ → ℝ} (hc : ContinuousOn D (Ioi 0))
    (hp : ∀ q, 0 < q → 0 < D q) (x : ℝ) :
    Continuous (fun y => genericAdditionalE D (f x^2) (f y^2)) := by
  have hf : Continuous (fun z : ℝ × UnitInterval =>
      D ((1-z.2.val)*f x^2+z.2.val*f z.1^2)) := by
    have hv : Continuous (fun z : ℝ × UnitInterval => z.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact hc.comp_continuous
      (((continuous_const.sub hv).mul_const (f x^2)).add
        (hv.mul ((continuous_f.comp continuous_fst).pow 2)))
      (fun z => affine_pos (sq_pos_of_pos (f_pos x)) (sq_pos_of_pos (f_pos z.1)) z.2)
  have hi : Continuous (fun y => ∫ θ : UnitInterval,
      D ((1-θ.val)*f x^2+θ.val*f y^2)) := by
    simpa only [setIntegral_univ] using
      (continuous_parametric_integral_of_continuous (μ := volume) hf isCompact_univ)
  exact hi.inv₀ (fun y => (mt inv_eq_zero.mpr) (genericAdditionalE_pos hc hp
    (sq_pos_of_pos (f_pos x)) (sq_pos_of_pos (f_pos y))).ne')

theorem scalar_minimum_off {B₀ D : ℝ → ℝ}
    (hc : ContinuousOn D (Ioi 0)) (hp : ∀ q, 0 < q → 0 < D q)
    (hd : ∀ q, 0 < q → HasDerivAt B₀ (-D q/2) q)
    (hb : ∀ x, B₀ (f x^2) = b x) {x y : ℝ} (hxy : x+y ≠ 0) :
    (b x+b y-(x-y)^2/(b x+b y+2*genericAdditionalE D (f x^2) (f y^2)))/2 =
      f x*f y/f (x+y) := by
  let e := genericAdditionalE D (f x^2) (f y^2)
  have he : 0 < e := genericAdditionalE_pos hc hp
    (sq_pos_of_pos (f_pos x)) (sq_pos_of_pos (f_pos y))
  have hrel := genericAdditionalE_difference hc hp hd
    (sq_pos_of_pos (f_pos x)) (sq_pos_of_pos (f_pos y))
  rw [hb, hb] at hrel
  change 2*e*(b x-b y) = f y^2-f x^2 at hrel
  have hA : 0 < b x+b y+2*e := by positivity [b_pos x, b_pos y]
  have hr : (b x-b y)*(b x+b y+2*e) = (x-y)*(x+y) := by
    nlinarith [b_sq x, b_sq y]
  rw [target_eq_of_add_ne_zero hxy]
  change (b x+b y-(x-y)^2/(b x+b y+2*e))/2 = (y*b x+x*b y)/(x+y)
  field_simp
  nlinarith [congrArg (fun z : ℝ => z*(x-y)) hr]

theorem scalar_minimum {B₀ D : ℝ → ℝ}
    (hc : ContinuousOn D (Ioi 0)) (hp : ∀ q, 0 < q → 0 < D q)
    (hd : ∀ q, 0 < q → HasDerivAt B₀ (-D q/2) q)
    (hb : ∀ x, B₀ (f x^2) = b x) (x y : ℝ) :
    (b x+b y-(x-y)^2/(b x+b y+2*genericAdditionalE D (f x^2) (f y^2)))/2 =
      f x*f y/f (x+y) := by
  by_cases hxy : x+y ≠ 0
  · exact scalar_minimum_off hc hp hd hb hxy
  have hy : y = -x := by
    have hz := not_ne_iff.mp hxy
    linarith
  subst y
  let L (y : ℝ) :=
    (b x+b y-(x-y)^2/(b x+b y+2*genericAdditionalE D (f x^2) (f y^2)))/2
  let R (y : ℝ) := f x*f y/f (x+y)
  have hL : Continuous L := by
    have hden : ∀ y, b x+b y+2*genericAdditionalE D (f x^2) (f y^2) ≠ 0 := by
      intro y
      exact ne_of_gt (by positivity [b_pos x, b_pos y,
        genericAdditionalE_pos hc hp (sq_pos_of_pos (f_pos x)) (sq_pos_of_pos (f_pos y))])
    exact (((continuous_const.add continuous_b).sub
      ((continuous_const.sub continuous_id).pow 2 |>.div
        ((continuous_const.add continuous_b).add
          ((continuous_genericAdditionalE_f hc hp x).const_mul 2)) hden)).div_const 2)
  have hR : Continuous R :=
    (continuous_const.mul continuous_f).div
      (continuous_f.comp (continuous_const.add continuous_id)) (fun y => (f_pos (x+y)).ne')
  have heq : L =ᶠ[𝓝[≠] (-x)] R := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    apply scalar_minimum_off hc hp hd hb
    simp only [mem_compl_iff, mem_singleton_iff] at hy
    intro h
    exact hy (by linarith)
  exact tendsto_nhds_unique
    (hL.continuousAt.mono_left nhdsWithin_le_nhds)
    ((hR.continuousAt.mono_left nhdsWithin_le_nhds).congr' heq.symm)

end

open DiagonalForms.System MeasureTheory Set Filter Topology Herglotz

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open DiagonalForms.System MeasureTheory Set Filter Topology


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.scalar_minimum := @_root_.OAI.EntropyPhotonNumber.scalar_minimum
