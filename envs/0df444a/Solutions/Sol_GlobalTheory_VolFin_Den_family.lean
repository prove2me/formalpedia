-- Prove2me | solution 1 for GlobalTheory.VolFin.Den.family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:53.637635+00:00
-- url     : https://prove2.me/submissions/159d5259-360a-4953-84bf-49b913bb02f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich
import Theorems.Thm_GlobalTheory_VolFin_Den_finset

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
namespace Den
theorem _root_.solution {R : ι → Subalgebra K F} {γ : ι → F} (h : Den R γ) {κ : Type} [Finite κ]
    (u : κ → F) : ∃ c, ∃ q ∈ piece R γ c, q ≠ 0 ∧ ∀ k, q * u k ∈ piece R γ c := by
  classical
  have := Fintype.ofFinite κ
  obtain ⟨c, q, hq, hq0, hs⟩ := h.finset (Finset.univ.image u)
  exact ⟨c, q, hq, hq0, fun k => hs _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))⟩
end Den
end GlobalTheory.VolFin
