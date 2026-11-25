-- Prove2me | solution 1 for KStar.Tree.nuOf_pos_of_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:37:11.367531+00:00
-- url     : https://prove2.me/submissions/d9ef058d-cebe-49ac-a0ad-c6783b993708

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuInf
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuBasic
import Theorems.Thm_KStar_Tree_le_nuOf_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Tree
variable {Γ : Type} [Group Γ] (l : ℕ) [Fact l.Prime] (ε : Γ →* ℤ_[l]ˣ) (n : ℕ)
namespace KStar.Tree
theorem _root_.solution (h : ∃ g, ε g ^ n ≠ 1) {K : Type} [CommRing K] [Nontrivial K] (θ : ℤ_[l] →+* K)
    (h1 : ∀ g, θ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n = 1) : 0 < nuOf l ε n := by
  have key := (le_nuOf_iff l ε n h 1).2 ?_
  · omega
  intro g
  rw [pow_one, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p]
  apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top θ)
  rw [RingHom.mem_ker, map_sub, map_pow, map_one, h1 g, sub_self]
end KStar.Tree
