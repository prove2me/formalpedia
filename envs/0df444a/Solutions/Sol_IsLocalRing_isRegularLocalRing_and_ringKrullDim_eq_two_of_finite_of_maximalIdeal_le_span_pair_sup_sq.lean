-- Prove2me | solution 1 for IsLocalRing.isRegularLocalRing_and_ringKrullDim_eq_two_of_finite_of_maximalIdeal_le_span_pair_sup_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/0853ab2f-19ea-58fe-b32d-261ac22efa73

import Mathlib
import Theorems.Thm_Algebra_IsIntegral_ringKrullDim_le_of_injective
import Theorems.Thm_IsLocalRing_maximalIdeal_eq_of_le_sup_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isRegularLocalRing_and_ringKrullDim_eq_two_of_finite_of_maximalIdeal_le_span_pair_sup_sq

set_option autoImplicit false

open IsLocalRing

theorem solution
    (S₀ : Type) [CommRing S₀] [IsDomain S₀] [IsNoetherianRing S₀] [IsLocalRing S₀] (hdim₀ : ringKrullDim S₀ = 2)
    (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra S₀ S] [Module.Finite S₀ S]
    (hinj : Function.Injective (algebraMap S₀ S))
    (ϖ y : S) (hgen : maximalIdeal S ≤ Ideal.span {ϖ, y} ⊔ maximalIdeal S ^ 2)
    (hϖ : ϖ ∈ maximalIdeal S) (hy : y ∈ maximalIdeal S) :
    IsRegularLocalRing S ∧ ringKrullDim S = 2 ∧ maximalIdeal S = Ideal.span {ϖ, y} := by
  classical
  haveI : Algebra.IsIntegral S₀ S := Algebra.IsIntegral.of_finite S₀ S
  have h2 : (2 : WithBot ℕ∞) ≤ ringKrullDim S := by
    rw [← hdim₀]; exact Algebra.IsIntegral.ringKrullDim_le_of_injective hinj
  have hN : Ideal.span {ϖ, y} ≤ maximalIdeal S := by
    rw [Ideal.span_le]
    intro z hz
    rcases hz with rfl | hz'
    · exact hϖ
    · rw [Set.mem_singleton_iff] at hz'; rw [hz']; exact hy
  have h𝔪 : maximalIdeal S = Ideal.span {ϖ, y} := IsLocalRing.maximalIdeal_eq_of_le_sup_sq _ hN hgen
  have hspan : (maximalIdeal S).spanFinrank ≤ 2 := by
    rw [h𝔪]
    refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)) ?_
    calc ({ϖ, y} : Set S).ncard ≤ ({y} : Set S).ncard + 1 := Set.ncard_insert_le ϖ {y}
      _ = 2 := by rw [Set.ncard_singleton]
  have hle : ((maximalIdeal S).spanFinrank : WithBot ℕ∞) ≤ ringKrullDim S :=
    le_trans (by exact_mod_cast hspan) h2
  haveI hreg : IsRegularLocalRing S := IsRegularLocalRing.of_spanFinrank_maximalIdeal_le S hle
  have hdim : ringKrullDim S = 2 := by
    have := (isRegularLocalRing_iff S).mp hreg
    refine le_antisymm ?_ h2
    rw [← this]; exact_mod_cast hspan
  exact ⟨hreg, hdim, h𝔪⟩

end S_IsLocalRing_isRegularLocalRing_and_ringKrullDim_eq_two_of_finite_of_maximalIdeal_le_span_pair_sup_sq
end P2MW
export P2MW.S_IsLocalRing_isRegularLocalRing_and_ringKrullDim_eq_two_of_finite_of_maximalIdeal_le_span_pair_sup_sq (solution)
