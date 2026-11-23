-- Prove2me | solution 1 for KStar.Tree.pow_nuOf_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:38.057738+00:00
-- url     : https://prove2.me/submissions/e24b50ed-9517-458b-8104-a468617f8950

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuInf
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuBasic

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
theorem _root_.solution (g : Γ) : (l : ℤ_[l]) ^ nuOf l ε n ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  rcases Nat.eq_zero_or_pos (nuOf l ε n) with h0 | hpos
  · rw [h0, pow_zero]
    exact one_dvd _
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hlt : k < nuOf l ε n := by omega
    have hnm : k ∉ {k | ∃ g, ¬ (l : ℤ_[l]) ^ (k + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1} :=
      Nat.notMem_of_lt_sInf hlt
    rw [hk]
    by_contra hd
    exact hnm ⟨g, hd⟩
end KStar.Tree
