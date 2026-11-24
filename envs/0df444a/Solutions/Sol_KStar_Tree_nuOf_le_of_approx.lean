-- Prove2me | solution 1 for KStar.Tree.nuOf_le_of_approx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:14.10434+00:00
-- url     : https://prove2.me/submissions/7ff864fd-257a-4b6d-97d7-002f9731a35e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuInf
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuSumApprox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Tree
variable (l : ℕ) [Fact l.Prime]
namespace KStar.Tree
theorem _root_.solution {Γ : Type} [Group Γ] (ε : Γ →* ℤ_[l]ˣ) (n m : ℕ) (u : ℤ_[l]ˣ)
    (h : ∀ k : ℕ, ∃ g, (l : ℤ_[l]) ^ k ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) - u)
    (hu : ¬ (l : ℤ_[l]) ^ (m + 1) ∣ (u : ℤ_[l]) ^ n - 1) : nuOf l ε n ≤ m := by
  obtain ⟨g, hg⟩ := h (m + 1)
  refine Nat.sInf_le ⟨g, fun hc => hu ?_⟩
  have h2 := hg.trans (sub_dvd_pow_sub_pow ((ε g : ℤ_[l]ˣ) : ℤ_[l]) (u : ℤ_[l]) n)
  have h3 := dvd_sub hc h2
  convert h3 using 1
  ring
end KStar.Tree
