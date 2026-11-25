-- Prove2me | solution 1 for GlobalTheory.HlCoc.exists_pow_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:51:26.61642+00:00
-- url     : https://prove2.me/submissions/4e70859d-bda5-4c6c-be65-d4121c33f860

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueCocycle
import Theorems.Thm_GlobalTheory_HlCoc_sndHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HlCoc.sndHom_apply

set_option autoImplicit false
open GlobalTheory GlobalTheory.HlCoc
open Topology
variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
variable [TopologicalSpace G] [TopologicalSpace M]
variable [IsTopologicalGroup G] [IsTopologicalAddGroup M] [ContinuousSMul G M]
namespace GlobalTheory.HlCoc
theorem _root_.solution {E : Type} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
    [T2Space E] (e : E) (l : ℕ) (hl : 0 < l)
    (hc : IsCompact ((Subgroup.zpowers e).topologicalClosure : Set E))
    (p : E) (hp : p ∈ (Subgroup.zpowers e).topologicalClosure) :
    ∃ j < l, ∃ q ∈ (Subgroup.zpowers e).topologicalClosure, p = e ^ j * q ^ l := by

  have hY : IsCompact (⋃ j ∈ Finset.range l,
      (fun q => e ^ j * q ^ l) '' ((Subgroup.zpowers e).topologicalClosure : Set E)) :=
    (Finset.range l).isCompact_biUnion fun j _ =>
      hc.image (continuous_const.mul (continuous_id.pow l))
  have hsub : ((Subgroup.zpowers e : Subgroup E) : Set E) ⊆ ⋃ j ∈ Finset.range l,
      (fun q => e ^ j * q ^ l) '' ((Subgroup.zpowers e).topologicalClosure : Set E) := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h0 : 0 ≤ n % (l : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hl.ne')
    have h1 : n % (l : ℤ) < l := Int.emod_lt_of_pos _ (by exact_mod_cast hl)
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_range]
    refine ⟨(n % l).toNat, by omega, e ^ (n / l),
      Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem_zpowers e _), ?_⟩
    simp only [← zpow_natCast]
    rw [Int.toNat_of_nonneg h0, ← zpow_mul, ← zpow_add, mul_comm, Int.emod_add_mul_ediv]
  have hmem := (closure_minimal hsub hY.isClosed)
    (by rw [← Subgroup.topologicalClosure_coe]; exact hp)
  simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_range] at hmem
  obtain ⟨j, hj, q, hq, hpq⟩ := hmem
  exact ⟨j, hj, q, hq, hpq.symm⟩
end GlobalTheory.HlCoc
