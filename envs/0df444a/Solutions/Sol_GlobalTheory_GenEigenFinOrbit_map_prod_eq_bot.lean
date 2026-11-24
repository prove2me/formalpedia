-- Prove2me | solution 1 for GlobalTheory.GenEigenFinOrbit.map_prod_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:11:16.436262+00:00
-- url     : https://prove2.me/submissions/ac219691-ad47-410f-a79a-6f43db70561a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanGenEigenOfFiniteDimensionalOrbit
import Theorems.Thm_GlobalTheory_GenEigenFinOrbit_map_prod_le
import Theorems.Thm_GlobalTheory_GenEigenFinOrbit_finrank_map_prod_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.GenEigenFinOrbit
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (G : Set (End ℂ V)) (N : Submodule ℂ V) (K : ℕ)
  (hcomm : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a)
  (hst : ∀ g ∈ G, N.map g ≤ N) (hnil : ∀ g ∈ G, ∀ n ∈ N, (g ^ K) n = 0)
include hcomm hst hnil
namespace GlobalTheory.GenEigenFinOrbit
theorem _root_.solution [FiniteDimensional ℂ N] (gs : List (End ℂ V))
    (hgs : ∀ g ∈ gs, g ∈ G) (hlen : finrank ℂ N ≤ gs.length) : N.map gs.prod = ⊥ := by
  haveI : FiniteDimensional ℂ (N.map gs.prod) :=
    Submodule.finiteDimensional_of_le (map_prod_le G N hst gs hgs)
  rw [← Submodule.finrank_eq_zero]
  have := finrank_map_prod_le G N K hcomm hst hnil gs hgs
  omega
end GlobalTheory.GenEigenFinOrbit
