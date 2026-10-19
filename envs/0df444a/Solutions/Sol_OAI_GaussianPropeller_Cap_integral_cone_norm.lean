-- Prove2me | solution 1 for OAI.GaussianPropeller.Cap.integral_cone_norm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:09:31.071426+00:00
-- url     : https://prove2.me/submissions/fc73f9f7-7b6e-4090-ad1d-ff6df620c32f

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/CapBounds.lean:L96-L122
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Cap.integral_cone_norm. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapBounds
import Theorems.Thm_OAI_GaussianPropeller_Polar_integral_homogeneous

-- ---- from OAI.Probability.GaussianPropeller.Polar ----
namespace OAI

universe uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

open Metric
namespace GaussianPropeller.Polar
open Translation

variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "S" => sphere (0 : E) 1
local notation "V" => (volume : Measure E)

end GaussianPropeller.Polar

namespace GaussianPropeller.Polar
open Real
lemma radial_eq (n : ℕ) {b : ℝ} (hb : 0<b) :
    radial n b = b ^ (-((n:ℝ)+1)/2) * (1/2) * Gamma (((n:ℝ)+1)/2) := by
  have hh := integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=n) (b:=b)
    (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) n]) hb
  simpa only [Real.rpow_natCast, Real.rpow_two, neg_mul, radial] using hh

lemma radial_pos (n : ℕ) {b : ℝ} (hb : 0<b) : 0<radial n b := by
  rw [radial_eq n hb]
  exact mul_pos (mul_pos (rpow_pos_of_pos hb _) (by norm_num))
    (Gamma_pos_of_pos (by positivity))

variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "S" => Metric.sphere (0:E) 1

end GaussianPropeller.Polar

end OAI

-- ---- from OAI.Probability.GaussianPropeller.CapBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Cap
open Coords OneCell ProbabilityBounds Polar
open scoped Topology
variable {n : ℕ}

lemma integral_cone_norm {d : ℕ} (hd : 0<d) (K : Set (CE d))
    (hK : MeasurableSet K) (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) :
    (∫ x : CE d, K.indicator (fun x => ‖x‖) x ∂stdGaussian (CE d)) =
      radial d (1/2)/radial (d-1) (1/2) * (stdGaussian (CE d)).real K := by
  let : NeZero d := ⟨by omega⟩
  have h0 := integral_homogeneous (ι:=Fin d) (K.indicator (fun _ => (1:ℝ))) 0 (by
    intro r hr x
    by_cases hx : x∈K <;> simp [hcone r hr x,hx])
  have h1 := integral_homogeneous (ι:=Fin d) (K.indicator (fun x => ‖x‖)) 1 (by
    intro r hr x
    by_cases hx : x∈K <;> simp [hcone r hr x,hx,norm_smul,Real.norm_eq_abs,abs_of_pos hr])
  have he : (fun θ : Metric.sphere (0:CE d) 1 => K.indicator (fun x => ‖x‖) θ.1) =
      fun θ : Metric.sphere (0:CE d) 1 => K.indicator (fun _ => (1:ℝ)) θ.1 := by
    funext θ
    by_cases hh : θ.1∈K <;> simp [hh, mem_sphere_zero_iff_norm.mp θ.2]
  rw [he] at h1
  simp only [Fintype.card_fin,Nat.add_zero,show d-1+1=d by omega] at h0 h1
  rw [integral_indicator hK,setIntegral_const,smul_eq_mul,mul_one] at h0
  have hr (q:ℕ) : (∫ r in Ioi (0:ℝ), r^q*Real.exp (-r^2/2))=radial q (1/2) := by
    unfold radial
    congr 1
    funext r; congr 2; ring
  rw [hr] at h0 h1
  rw [h1,h0]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (radial_pos (d-1) (b:=1/2) (by norm_num)).ne').mpr
  ring

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

end GaussianPropeller.Cap

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Cap
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open Coords OneCell ProbabilityBounds Polar
open scoped Topology


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Cap.integral_cone_norm := @_root_.OAI.GaussianPropeller.Cap.integral_cone_norm
