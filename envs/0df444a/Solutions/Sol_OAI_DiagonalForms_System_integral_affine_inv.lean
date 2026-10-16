-- Prove2me | solution 1 for OAI.DiagonalForms.System.integral_affine_inv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:12:56.273627+00:00
-- url     : https://prove2.me/submissions/ac238de9-9af0-4cf4-ad17-92b29086ca74

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiagonalForms.lean:L603-L616
-- (upload_full_project.md Phase 4): solution for node OAI.DiagonalForms.System.integral_affine_inv. The node keeps its source
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

theorem integral_affine_inv {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    (∫ t : UnitInterval, ((1-t.val)*X+t.val*Y)⁻¹) = (logMean X Y)⁻¹ := by
  rw [integral_unitInterval (fun t => ((1-t)*X+t*Y)⁻¹)]
  by_cases he : X = Y
  · subst Y
    simp only [logMean]
    conv_lhs => arg 1; ext t; rw [show (1-t)*X+t*X = X by ring]
    simp
  · have hd : Y-X ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
    conv_lhs => arg 1; ext t; rw [show (1-t)*X+t*Y = (Y-X)*t+X by ring]
    rw [intervalIntegral.integral_comp_mul_add _ hd]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
    rw [integral_inv_of_pos hX hY, Real.log_div hY.ne' hX.ne']
    simp [logMean, he, div_eq_mul_inv, mul_comm]

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

-- ---- platform node ----
open OAI OAI.DiagonalForms OAI.DiagonalForms.System
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
open MeasureTheory Set


theorem solution : type_of% @_root_.OAI.DiagonalForms.System.integral_affine_inv := @_root_.OAI.DiagonalForms.System.integral_affine_inv
