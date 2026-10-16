-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.genericAdditionalE_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:30:25.889404+00:00
-- url     : https://prove2.me/submissions/f955d107-8767-4d57-934b-f0bc5cae4a91

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Interpolation.lean:L410-L423
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.genericAdditionalE_pos. The node keeps its source
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
theorem unitInterval_volume : (volume : Measure UnitInterval) Set.univ = 1 := by
  simp [UnitInterval]

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

theorem genericAdditionalE_pos {D : ℝ → ℝ} (hc : ContinuousOn D (Ioi 0))
    (hp : ∀ q, 0 < q → 0 < D q) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    0 < genericAdditionalE D s t := by
  apply inv_pos.mpr
  have hct : Continuous (fun θ : UnitInterval => D ((1-θ.val)*s+θ.val*t)) :=
    hc.comp_continuous (by fun_prop) (affine_pos hs ht)
  have hsup : Function.support (fun θ : UnitInterval => D ((1-θ.val)*s+θ.val*t)) = univ := by
    ext θ
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hp _ (affine_pos hs ht θ)).ne'
  rw [integral_pos_iff_support_of_nonneg (fun θ => (hp _ (affine_pos hs ht θ)).le)
    (hct.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), hsup,
    unitInterval_volume]
  norm_num

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


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.genericAdditionalE_pos := @_root_.OAI.EntropyPhotonNumber.genericAdditionalE_pos
