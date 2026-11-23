-- Prove2me | solution 1 for GlobalTheory.BK.derivative_mem_R
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:01.719876+00:00
-- url     : https://prove2.me/submissions/fb06c6bf-c667-4b16-8437-01dccfacb654

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_rad_nonneg
import Theorems.Thm_GlobalTheory_BK_mem_R
import Theorems.Thm_GlobalTheory_BK_rad_pos
import Theorems.Thm_GlobalTheory_BK_norm_coeff_derivative_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}
namespace GlobalTheory.BK
theorem _root_.solution (l : ℕ) [Fact l.Prime] {k : ℝ} {f : K⟦X⟧} (hf : f ∈ R O K l k) :
    PowerSeries.derivative K f ∈ R O K l k := by
  have h := ((mem_R.1 hf).comp (tendsto_add_atTop_nat 1)).mul_const (rad l k)⁻¹
  rw [zero_mul] at h
  refine mem_R.2 <| squeeze_zero
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (rad_nonneg l k) n)) (fun n => ?_) h
  have := rad_pos l k
  calc _ ≤ ‖coeff (n + 1) f‖ * rad l k ^ n := by gcongr; exact norm_coeff_derivative_le f n
    _ = _ := by simp only [Function.comp]; field_simp; ring
end GlobalTheory.BK
