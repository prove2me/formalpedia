-- Prove2me | solution 1 for GlobalTheory.mem_saturation_iff_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:41:08.684223+00:00
-- url     : https://prove2.me/submissions/67c73a95-6c94-46b2-9b07-254a5ad18917

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_map_subtype_saturation_eq_inf_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
namespace GlobalTheory
theorem _root_.solution {M : Submodule R V} {N : Submodule R M} {x : M} :
    x ∈ saturation N ↔ (x : V) ∈ Submodule.span K (N.map M.subtype : Set V) := by
  have e := map_subtype_saturation_eq_inf_span K M N
  constructor
  · intro hx
    have hx' : (x : V) ∈ (saturation N).map M.subtype := Submodule.mem_map_of_mem hx
    rw [e] at hx'
    exact (Submodule.mem_inf.1 hx').2
  · intro hx
    have hx' : (x : V) ∈ M ⊓ (Submodule.span K (N.map M.subtype : Set V)).restrictScalars R :=
      Submodule.mem_inf.2 ⟨x.2, hx⟩
    rw [← e] at hx'
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx'
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy
end GlobalTheory
