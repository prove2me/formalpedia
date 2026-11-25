-- Prove2me | solution 1 for GroundTheory.LocalField.integrable_mul_char_of_mem_schwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:49.445508+00:00
-- url     : https://prove2.me/submissions/f379c41d-ab2d-4758-a752-9fdaf8506d38

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
variable (ψ : AddChar K Circle)
variable {ψ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1
omit hψ1
namespace GroundTheory.LocalField
theorem _root_.solution {f : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (y : K) : Integrable (fun x => f x * (ψ (x * y) : ℂ)) μ :=
  (hf.1.continuous.mul ((continuous_subtype_val.comp hψ).comp
    (continuous_id.mul continuous_const))).integrable_of_hasCompactSupport hf.2.mul_right
end GroundTheory.LocalField
