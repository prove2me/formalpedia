-- Prove2me | solution 1 for OAI.Paper256.inverse_sqrt_affine_scalar_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:00:27.826306+00:00
-- url     : https://prove2.me/submissions/a4dbcc65-ca2c-442e-bba9-1f7350e7665a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/SpectralContinuity.lean:L35-L48
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.inverse_sqrt_affine_scalar_tendsto. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth
import Definitions.Def_OAI_Analysis_HyperbolicCones_TangentBasic

-- ---- from OAI.Analysis.HyperbolicCones.SpectralContinuity ----
namespace OAI

/-! Finite spectral convergence, including eigenvalues equal to zero. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology
universe u

namespace Paper256

theorem inverse_sqrt_affine_scalar_tendsto (μ : ℝ) (hμ : 0 ≤ μ) :
    Tendsto (fun t : ℝ => (Real.sqrt (1 + (t - 1) * μ))⁻¹) atTop
      (𝓝 (if μ = 0 then 1 else 0)) := by
  by_cases hzero : μ = 0
  · simp [hzero]
  · have hpos : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hzero)
    have haff : Tendsto (fun t : ℝ => 1 + (t - 1) * μ) atTop atTop := by
      have hm := (tendsto_id.const_mul_atTop hpos).atTop_add
        (tendsto_const_nhds (x := 1 - μ))
      convert hm using 1
      ext t
      simp only [id_eq]
      ring
    simpa [hzero, Function.comp_def] using tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp haff)

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology


theorem solution : type_of% @_root_.OAI.Paper256.inverse_sqrt_affine_scalar_tendsto := @_root_.OAI.Paper256.inverse_sqrt_affine_scalar_tendsto
