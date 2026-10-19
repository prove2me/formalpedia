-- Prove2me | solution 1 for OAI.DirectCrouzeix.Faber.integral_inner_positiveSeries
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:27:21.995876+00:00
-- url     : https://prove2.me/submissions/8d0707fc-7c65-4240-9390-3c9077dfa0ad

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/KernelContraction.lean:L133-L149
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Faber.integral_inner_positiveSeries. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction

-- ---- from OAI.Analysis.DirectCrouzeix.CompactIntegrals ----
namespace OAI

universe u_87 u_88 u_89 u_90 u_91 u_92 u_93

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem integrable_of_continuous_compact {α : Type u_87} {E : Type u_88} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [CompactSpace α]
    [NormedAddCommGroup E] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.KernelContraction ----
namespace OAI

universe u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section Hilbert

variable {E : Type u_127} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem integral_inner_positiveSeries {N : ℕ} (C : Fin N → E)
    (f : Angle → E) (hf : Continuous f) :
    (∫ t, inner ℂ (positiveSeries C t) (f t) ∂angularMeasure) =
      ∑ k, inner ℂ (C k) (fourierCoeff f (k:ℤ)) := by
  simp only [positiveSeries,sum_inner,inner_smul_left,← fourier_neg]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    have he : (fun t => fourier (-(k:ℤ)) t * inner ℂ (C k) (f t)) =
        (fun t => inner ℂ (C k) (fourier (-(k:ℤ)) t • f t)) := by
      funext t; simp only [inner_smul_right]
    rw [he,integral_inner]
    · rfl
    · exact integrable_of_continuous_compact _ ((fourier (-(k:ℤ))).continuous.smul hf)
  · intro k hk
    exact integrable_of_continuous_compact _
      ((fourier (-(k:ℤ))).continuous.mul (continuous_const.inner hf))

end Hilbert

section FaberHilbert

variable {E : Type u_128} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FaberHilbert

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Faber.integral_inner_positiveSeries := @_root_.OAI.DirectCrouzeix.Faber.integral_inner_positiveSeries
