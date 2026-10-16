-- Prove2me | solution 1 for OAI.Paper256.kernel_projection_tangent_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:47:21.366976+00:00
-- url     : https://prove2.me/submissions/dd14e477-059c-450a-aeaa-6ec67d2dfd2d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/KernelTangent.lean:L13-L34
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.kernel_projection_tangent_derivative. The node keeps its source
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
import Theorems.Thm_OAI_Paper256_kernel_projection_smooth_local_extension

-- ---- from OAI.Analysis.HyperbolicCones.TangentBasic ----
namespace OAI

noncomputable section

open scoped RealInnerProductSpace

namespace Paper256

theorem tangentCurve_unit (v h : Vec 4) (hv : ‖v‖ = 1)
    (hh : inner ℝ v h = 0) (s : ℝ) : ‖tangentCurve v h s‖ = 1 := by
  have hp : 0 < 1 + s ^ 2 * ‖h‖ ^ 2 := by positivity
  have hn : ‖v + s • h‖ = Real.sqrt (1 + s ^ 2 * ‖h‖ ^ 2) := by
    symm
    apply (Real.sqrt_eq_iff_eq_sq hp.le (norm_nonneg _)).2
    symm
    rw [norm_add_sq_real, real_inner_smul_right, hh, hv, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [tangentCurve, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (Real.sqrt_pos.2 hp), hn, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 hp))]

theorem tangentCurve_derivative (v h : Vec 4) : HasDerivAt (tangentCurve v h) h 0 := by
  have hg : HasDerivAt (fun s : ℝ => 1 + s ^ 2 * ‖h‖ ^ 2) 0 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖h‖ ^ 2)).const_add 1
  have hs : HasDerivAt (fun s : ℝ => (Real.sqrt (1 + s ^ 2 * ‖h‖ ^ 2))⁻¹) 0 0 := by
    simpa using! (hg.sqrt (by norm_num)).inv (by norm_num)
  simpa [tangentCurve] using! hs.smul (((hasDerivAt_id (0 : ℝ)).smul_const h).const_add v)

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.KernelTangent ----
namespace OAI

noncomputable section

open scoped ContDiff Topology RealInnerProductSpace Matrix.Norms.L2Operator
open Set Filter

namespace Paper256

theorem kernel_projection_tangent_derivative (c : ℕ) (hC : 0 < c)
    (E : Sym 4 →ₗ[ℝ] Sym c) :
    ∃ (v : Vec 4) (T : Vec 4 →ₗ[ℝ] Mat c ℝ),
      ‖v‖ = 1 ∧ v 0 ≠ 0 ∧ ∀ h : Vec 4, inner ℝ v h = 0 →
        HasDerivAt (fun s : ℝ => kernelProjection
          (E (1 - outerSym (tangentCurve v h s)) : Mat c ℝ)) (T h) 0 := by
  obtain ⟨v, U, F, hv, hv0, hU, hvU, hF, heq⟩ :=
    kernel_projection_smooth_local_extension c hC E
  have hd : DifferentiableAt ℝ F v :=
    (hF.contDiffAt (hU.mem_nhds hvU)).differentiableAt (by norm_num)
  refine ⟨v, (fderiv ℝ F v).toLinearMap, hv, hv0, ?_⟩
  intro h hh
  have hc := tangentCurve_derivative v h
  have hcomp : HasDerivAt (fun s => F (tangentCurve v h s)) ((fderiv ℝ F v) h) 0 := by
    simpa only [Function.comp_apply] using!
      hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (by simp [tangentCurve])
  apply hcomp.congr_of_eventuallyEq
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), tangentCurve v h s ∈ U := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa [tangentCurve] using hU.mem_nhds hvU
  filter_upwards [hmem] with s hs
  exact (heq _ hs (tangentCurve_unit v h hv hh s)).symm

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped ContDiff Topology RealInnerProductSpace Matrix.Norms.L2Operator
open Set Filter


theorem solution : type_of% @_root_.OAI.Paper256.kernel_projection_tangent_derivative := @_root_.OAI.Paper256.kernel_projection_tangent_derivative
