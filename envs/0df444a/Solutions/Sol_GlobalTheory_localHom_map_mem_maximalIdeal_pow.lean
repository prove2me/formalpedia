-- Prove2me | solution 1 for GlobalTheory.localHom_map_mem_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:18:57.731997+00:00
-- url     : https://prove2.me/submissions/57680024-6e01-4e2b-a00f-21e822c454a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HenselRootsCompatible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A V : Type} [CommRing A] [IsLocalRing A] [CommRing V]
    [IsLocalRing V] (α : A →+* V) [IsLocalHom α] (n : ℕ) {x : A}
    (hx : x ∈ maximalIdeal A ^ n) : α x ∈ maximalIdeal V ^ n := by
  have h1 : (maximalIdeal A).map α ≤ maximalIdeal V := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    exact map_nonunit α y hy
  have := Ideal.mem_map_of_mem α hx
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h1 n this
end GlobalTheory
