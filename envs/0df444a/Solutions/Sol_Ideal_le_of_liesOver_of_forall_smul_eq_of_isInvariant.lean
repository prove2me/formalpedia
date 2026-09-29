-- Prove2me | solution 1 for Ideal.le_of_liesOver_of_forall_smul_eq_of_isInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1d0ff101-f015-5bfb-8e53-c3089d4ebbdd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_le_of_liesOver_of_forall_smul_eq_of_isInvariant

set_option autoImplicit false

open scoped Pointwise

theorem solution
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (𝔭₀ 𝔭₁ : Ideal B) [𝔭₀.IsPrime] [𝔭₁.IsPrime]
    (h₀ : ∀ g : G, g • 𝔭₀ = 𝔭₀) (h₁ : ∀ g : G, g • 𝔭₁ = 𝔭₁)
    (y : Ideal A) [y.IsPrime] (hy₀ : 𝔭₀.under A ≤ y) (hy₁ : 𝔭₁.under A ≤ y)
    (Q : Ideal B) [Q.IsPrime] (hQ : Q.under A = y) :
    𝔭₀ ≤ Q ∧ 𝔭₁ ≤ Q := by
  haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G

  have key : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], (∀ g : G, g • 𝔭 = 𝔭) → 𝔭.under A ≤ y → 𝔭 ≤ Q := by
    intro 𝔭 _ hstab hle
    obtain ⟨Q', hQ'𝔭, hQ'prime, hQ'y⟩ := Ideal.exists_ideal_over_prime_of_isIntegral y 𝔭 hle
    haveI := hQ'prime

    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G Q' Q (by rw [Ideal.under_def, Ideal.under_def, hQ'y, ← hQ, Ideal.under_def])
    rw [hg, ← hstab g]
    exact Ideal.pointwise_smul_le_pointwise_smul_iff.mpr hQ'𝔭
  exact ⟨key 𝔭₀ h₀ hy₀, key 𝔭₁ h₁ hy₁⟩

end S_Ideal_le_of_liesOver_of_forall_smul_eq_of_isInvariant
end P2MW
export P2MW.S_Ideal_le_of_liesOver_of_forall_smul_eq_of_isInvariant (solution)
