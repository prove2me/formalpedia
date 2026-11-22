-- Prove2me | solution 1 for IsSigmaOrderContinuousNorm.tendsto_of_monotone_isLUB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:34.880089+00:00
-- url     : https://prove2.me/submissions/299d8b39-1f36-4efe-8718-0cfaece9ac57

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
theorem _root_.solution {u : ℕ → X} {x : X}
    (hmono : Monotone u) (hlub : IsLUB (Set.range u) x) :
    Filter.Tendsto u Filter.atTop (nhds x) := by
  -- Define v n = x - u n, which is antitone, nonneg, with GLB 0
  have hv_anti : Antitone (fun n => x - u n) :=
    fun _ _ h => sub_le_sub_left (hmono h) x
  have hv_nn : ∀ n, 0 ≤ x - u n :=
    fun n => sub_nonneg.mpr (hlub.1 ⟨n, rfl⟩)
  have hv_glb : IsGLB (Set.range (fun n => x - u n)) 0 := by
    constructor
    · rintro _ ⟨n, rfl⟩; exact hv_nn n
    · intro w hw
      have hlb : ∀ y ∈ Set.range u, y ≤ x - w := by
        rintro _ ⟨n, rfl⟩
        exact le_sub_comm.mp (hw ⟨n, rfl⟩)
      have h := hlub.2 hlb
      rwa [le_sub_iff_add_le, add_comm, add_le_iff_nonpos_left] at h
  have htv := tendsto_of_antitone_isGLB_zero hv_anti hv_nn hv_glb
  convert htv.const_sub x using 1
  · ext n; abel
  · abel_nf
end IsSigmaOrderContinuousNorm
