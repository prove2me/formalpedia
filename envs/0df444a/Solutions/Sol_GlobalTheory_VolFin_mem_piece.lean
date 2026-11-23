-- Prove2me | solution 1 for GlobalTheory.VolFin.mem_piece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:43.519796+00:00
-- url     : https://prove2.me/submissions/4fad1281-be8f-490f-a7d0-d4ae537f0f9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.VolFin
open Module Filter Topology
variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {ι : Type}
namespace GlobalTheory.VolFin
theorem _root_.solution {R : ι → Subalgebra K F} {γ : ι → F} {e : ℕ} {f : F} :
    f ∈ piece R γ e ↔ ∀ i, f * γ i ^ e ∈ R i := Iff.rfl
end GlobalTheory.VolFin
