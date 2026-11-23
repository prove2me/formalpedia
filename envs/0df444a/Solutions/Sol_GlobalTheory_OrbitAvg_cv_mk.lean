-- Prove2me | solution 1 for GlobalTheory.OrbitAvg.cv_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:35.175904+00:00
-- url     : https://prove2.me/submissions/cf9117f1-6393-45a1-80ec-cb3230a85141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
import Theorems.Thm_GlobalTheory_OrbitAvg_mem_stab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitAvg
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)
namespace GlobalTheory.OrbitAvg
theorem _root_.solution {H : Subgroup L} {x : V} (hH : H ≤ stab π L x) (a : L) :
    cv π L H x (QuotientGroup.mk a) = π (a : G) x := by
  unfold cv
  set b : L := (QuotientGroup.mk a : L ⧸ H).out with hb
  have h1 : (QuotientGroup.mk b : L ⧸ H) = QuotientGroup.mk a := QuotientGroup.out_eq' _
  have h2 : b⁻¹ * a ∈ H := QuotientGroup.eq.mp h1
  have h3 := (mem_stab π L).mp (hH h2)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply] at h3
  calc π (b : G) x = π (b : G) (π (b : G)⁻¹ (π (a : G) x)) := by rw [h3]
    _ = π (a : G) x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
end GlobalTheory.OrbitAvg
