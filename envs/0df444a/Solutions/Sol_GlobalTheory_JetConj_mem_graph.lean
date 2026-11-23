-- Prove2me | solution 1 for GlobalTheory.JetConj.mem_graph
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:44.866796+00:00
-- url     : https://prove2.me/submissions/479ae943-13ac-46dd-a97d-ffd7483e1013

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.JetConj
namespace GlobalTheory.JetConj
theorem _root_.solution {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {a b : ℂ} :
    (a, b) ∈ graph M ρ ↔ ∃ h : a ∈ M, ρ ⟨a, h⟩ = b := by
  simp only [graph, RingHom.mem_range, RingHom.prod_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, hy⟩
    subst hx
    exact ⟨x.2, hy⟩
  · rintro ⟨h, hb⟩
    exact ⟨⟨a, h⟩, rfl, hb⟩
end GlobalTheory.JetConj
