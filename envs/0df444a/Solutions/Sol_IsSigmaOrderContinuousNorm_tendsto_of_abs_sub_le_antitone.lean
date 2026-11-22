-- Prove2me | solution 1 for IsSigmaOrderContinuousNorm.tendsto_of_abs_sub_le_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:18.306207+00:00
-- url     : https://prove2.me/submissions/1ff5a85a-0e9f-4c79-97b1-2118674ac4ec

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Basic

set_option autoImplicit true
@[expose] public section
public section
universe u
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open IsSigmaOrderContinuousNorm
variable [NormedVectorLattice X] [IsSigmaOrderContinuousNorm X]
namespace IsSigmaOrderContinuousNorm
theorem _root_.solution {u : ℕ → X} {v : ℕ → X} {x : X}
    (hv_anti : Antitone v) (hv_nn : ∀ n, 0 ≤ v n)
    (hv_glb : IsGLB (Set.range v) 0)
    (hle : ∀ n, |u n - x| ≤ v n) :
    Filter.Tendsto u Filter.atTop (nhds x) := by
  have hv_tend := tendsto_of_antitone_isGLB_zero hv_anti hv_nn hv_glb
  have hnorm_le : ∀ n, ‖u n - x‖ ≤ ‖v n‖ := fun n =>
    norm_le_norm_of_abs_le_abs ((hle n).trans (le_abs_self _))
  have hv_norm := hv_tend.norm
  rw [norm_zero] at hv_norm
  have h0 := squeeze_zero_norm hnorm_le hv_norm
  exact tendsto_sub_nhds_zero_iff.mp h0
end IsSigmaOrderContinuousNorm
