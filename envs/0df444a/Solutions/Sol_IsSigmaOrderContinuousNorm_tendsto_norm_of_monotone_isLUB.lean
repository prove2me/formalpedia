-- Prove2me | solution 1 for IsSigmaOrderContinuousNorm.tendsto_norm_of_monotone_isLUB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:19.099803+00:00
-- url     : https://prove2.me/submissions/a3948a5b-d160-4f01-8eb8-b6efd5d4955d

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Basic
public import Theorems.Thm_IsSigmaOrderContinuousNorm_tendsto_of_monotone_isLUB

set_option autoImplicit true
@[expose] public section
public section
universe u
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open IsSigmaOrderContinuousNorm
variable [NormedVectorLattice X] [IsSigmaOrderContinuousNorm X]
namespace IsSigmaOrderContinuousNorm
theorem _root_.solution {u : ℕ → X} {x : X}
    (hmono : Monotone u)
    (hlub : IsLUB (Set.range u) x) :
    Filter.Tendsto (fun n => ‖u n‖) Filter.atTop (nhds ‖x‖) :=
  (tendsto_of_monotone_isLUB hmono hlub).norm
end IsSigmaOrderContinuousNorm
