-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.inverseExterior_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:24:02.083187+00:00
-- url     : https://prove2.me/submissions/7f5f0202-686f-4b92-a7eb-6f453218aafc

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/InverseExterior.lean:L48-L76
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.inverseExterior_isOpen. The node keeps its source
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_NormalFamilies
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExtremalEmbedding
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DiskMapping
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PoissonBoundary
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HarmonicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HolomorphicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ConformalCollar
import Definitions.Def_OAI_Analysis_DirectCrouzeix_AnalyticCharts
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExponentialLevels
import Definitions.Def_OAI_Analysis_DirectCrouzeix_InverseExterior

-- ---- from OAI.Analysis.DirectCrouzeix.InverseExterior ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

theorem mem_inverseExterior_iff {f : ℂ → ℝ} {a w : ℂ} (hw : w ≠ 0) :
    w ∈ inverseExterior f a ↔ 1 < f (a+w⁻¹) := or_iff_right hw

theorem inverseExterior_isOpen {f : ℂ → ℝ} (hf : Continuous f)
    (hc : IsCompact {z | f z ≤ 1}) (a : ℂ) : IsOpen (inverseExterior f a) := by
  obtain ⟨M,hM,hbound⟩ := hc.isBounded.exists_pos_norm_le
  rw [isOpen_iff_mem_nhds]
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    let r := (M+‖a‖+1)⁻¹
    have hr : 0 < r := inv_pos.mpr (by positivity)
    apply mem_of_superset (ball_mem_nhds (0:ℂ) hr)
    intro w hw
    by_cases hw0 : w = 0
    · exact Or.inl hw0
    apply Or.inr
    by_contra hn
    have hh := hbound (a+w⁻¹) (le_of_not_gt hn)
    have hnorm : ‖w⁻¹‖ ≤ M+‖a‖ := by
      calc
        ‖w⁻¹‖ = ‖(a+w⁻¹)-a‖ := by congr 1; abel
        _ ≤ ‖a+w⁻¹‖+‖a‖ := norm_sub_le _ _
        _ ≤ M+‖a‖ := add_le_add_left hh _
    have hrw : ‖w‖ < (M+‖a‖+1)⁻¹ := mem_ball_zero_iff.mp hw
    have hlarge : M+‖a‖+1 < ‖w‖⁻¹ := (lt_inv_comm₀ (norm_pos_iff.mpr hw0) (by positivity)).mp hrw
    rw [norm_inv] at hnorm
    linarith
  · have hc' : ContinuousAt (fun w : ℂ => f (a+w⁻¹)) w :=
      hf.continuousAt.comp (continuousAt_const.add (continuousAt_id.inv₀ hw0))
    have he : ∀ᶠ y in 𝓝 w, 1 < f (a+y⁻¹) := continuousAt_const.eventually_lt hc' ((mem_inverseExterior_iff hw0).mp hw)
    exact mem_of_superset he (fun y hy => Or.inr hy)

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Geometry
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.inverseExterior_isOpen := @_root_.OAI.DirectCrouzeix.Geometry.inverseExterior_isOpen
