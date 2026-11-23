-- Prove2me | solution 1 for GlobalTheory.CycSpanFin.pow_mem_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:35.251554+00:00
-- url     : https://prove2.me/submissions/8c4d3c96-60fc-44ec-a12e-c7462c4809cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CycSpanFin
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CycSpanFin
theorem _root_.solution (T : Module.End ℂ V) {d k : ℕ} (hk : k ≤ d) {N : Submodule ℂ V} {v : V} (hv : v ∈ N) :
    (T ^ k) v ∈ ext T d N :=
  Submodule.mem_iSup_of_mem (⟨k, by omega⟩ : Fin (d + 1)) (Submodule.mem_map_of_mem hv)
end GlobalTheory.CycSpanFin
