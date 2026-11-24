-- Prove2me | solution 1 for GlobalTheory.ArchChar.tendsto_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:46.8778+00:00
-- url     : https://prove2.me/submissions/da21f8a2-2a0e-42a1-a6ba-85618e299817

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousCharUnitsComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CharConstOnTranslatesTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.ArchChar
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ArchChar
theorem _root_.solution {α : Type} {l : Filter α} (θ : ℂ) (r C : ℝ) {a μ : α → ℝ}
    (hμ : Tendsto μ l atTop) (h : ∀ m, |a m - μ m * r| ≤ C) :
    Tendsto (fun m => ((a m : ℂ) + θ) / (μ m : ℂ)) l (𝓝 (r : ℂ)) := by
  have hev : ∀ᶠ m in l, 0 < μ m := hμ.eventually_gt_atTop 0
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : Tendsto (fun m => (C + ‖θ‖) / μ m) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hμ
  refine squeeze_zero' (Eventually.of_forall fun m => norm_nonneg _) ?_ hbound
  filter_upwards [hev] with m hm
  have hμc : (μ m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hid : ((a m : ℂ) + θ) / (μ m : ℂ) - (r : ℂ) = (((a m - μ m * r : ℝ) : ℂ) + θ) / (μ m : ℂ) := by
    field_simp
    push_cast
    ring
  rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
  gcongr
  calc ‖((a m - μ m * r : ℝ) : ℂ) + θ‖ ≤ ‖((a m - μ m * r : ℝ) : ℂ)‖ + ‖θ‖ := norm_add_le _ _
    _ ≤ C + ‖θ‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      linarith [h m]
end GlobalTheory.ArchChar
