-- Prove2me | solution 1 for OAI.Paper256.norm_sq_derivative_of_quadratic_curve
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:48:58.574698+00:00
-- url     : https://prove2.me/submissions/95eddf52-bf32-47be-b97e-a1127e7b5d36

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/TangentLimit.lean:L14-L33
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.norm_sq_derivative_of_quadratic_curve. The node keeps its source
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

-- ---- from OAI.Analysis.HyperbolicCones.TangentLimit ----
namespace OAI

noncomputable section

open scoped Topology
open Filter

universe u

namespace Paper256

theorem norm_sq_derivative_of_quadratic_curve
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (v : F) (α β : ℝ) (hβ : 0 ≤ β)
    (hf : HasDerivAt f v 0) (hzero : f 0 = 0)
    (hval : ∀ s : ℝ, ‖f s‖ ^ 2 = s ^ 2 / (1 + s ^ 2 * β) * α) :
    ‖v‖ ^ 2 = α := by
  have ht : Tendsto (fun s : ℝ => ‖s⁻¹ • f s‖ ^ 2) (𝓝[≠] 0) (𝓝 (‖v‖ ^ 2)) := by
    simpa only [zero_add, hzero, sub_zero] using hf.tendsto_slope_zero.norm.pow 2
  have hc : ContinuousAt (fun s : ℝ => α / (1 + s ^ 2 * β)) 0 := by
    fun_prop (disch := norm_num)
  have hr : Tendsto (fun s : ℝ => α / (1 + s ^ 2 * β)) (𝓝[≠] 0) (𝓝 α) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have he : (fun s : ℝ => ‖s⁻¹ • f s‖ ^ 2) =ᶠ[𝓝[≠] 0]
      (fun s : ℝ => α / (1 + s ^ 2 * β)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := hs
    have hd : 1 + s ^ 2 * β ≠ 0 := ne_of_gt (by positivity)
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hval]
    field_simp
  exact tendsto_nhds_unique ht (hr.congr' he.symm)

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped Topology
open Filter


theorem solution.{u} : type_of% @_root_.OAI.Paper256.norm_sq_derivative_of_quadratic_curve.{u} := @_root_.OAI.Paper256.norm_sq_derivative_of_quadratic_curve.{u}
