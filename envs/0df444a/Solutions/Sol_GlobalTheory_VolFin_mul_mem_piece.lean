-- Prove2me | solution 1 for GlobalTheory.VolFin.mul_mem_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:11:52.588806+00:00
-- url     : https://prove2.me/submissions/83db93db-be7e-4053-b728-1dcc7d54f315

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich
import Theorems.Thm_GlobalTheory_VolFin_mem_piece

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
theorem _root_.solution {R : ι → Subalgebra K F} {γ : ι → F} {e e' : ℕ} {a b : F}
    (ha : a ∈ piece R γ e) (hb : b ∈ piece R γ e') : a * b ∈ piece R γ (e + e') := mem_piece.2 fun i => by
  have hab := (R i).mul_mem (mem_piece.1 ha i) (mem_piece.1 hb i)
  rw [pow_add]
  convert hab using 1
  ring
end GlobalTheory.VolFin
