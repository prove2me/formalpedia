-- Prove2me | solution 1 for IsSigmaOrderContinuousNorm.tendsto_of_antitone_isGLB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:35.193665+00:00
-- url     : https://prove2.me/submissions/a8fb7f6d-0052-4150-8721-8cdebffa2100

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Basic
public import Theorems.Thm_OrderConvergesTo_add


set_option autoImplicit true
@[expose] public section
public section
universe u
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open IsSigmaOrderContinuousNorm
variable [NormedVectorLattice X] [IsSigmaOrderContinuousNorm X]
namespace IsSigmaOrderContinuousNorm
theorem _root_.solution {u : ℕ → X} {x : X}
    (hanti : Antitone u) (hglb : IsGLB (Set.range u) x) :
    Filter.Tendsto u Filter.atTop (nhds x) := by
  have hv_anti : Antitone (fun n => u n - x) :=
    fun _ _ h => sub_le_sub_right (hanti h) x
  have hv_nn : ∀ n, 0 ≤ u n - x :=
    fun n => sub_nonneg.mpr (hglb.1 ⟨n, rfl⟩)
  have hv_glb : IsGLB (Set.range (fun n => u n - x)) 0 := by
    constructor
    · rintro _ ⟨n, rfl⟩; exact hv_nn n
    · intro w hw
      have hlb : ∀ y ∈ Set.range u, w + x ≤ y := by
        rintro _ ⟨n, rfl⟩
        exact add_le_of_le_sub_right (hw ⟨n, rfl⟩)
      have h := hglb.2 hlb
      rwa [add_le_iff_nonpos_left] at h
  have htv := tendsto_of_antitone_isGLB_zero hv_anti hv_nn hv_glb
  convert htv.add tendsto_const_nhds using 1
  · ext n; abel
  · abel_nf
end IsSigmaOrderContinuousNorm
