-- Prove2me | solution 1 for GlobalTheory.QuadraticEtale.exists_isUnit_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:03:08.732722+00:00
-- url     : https://prove2.me/submissions/3aff19bc-9a29-4854-99fe-0a9530b30dd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsUnitFormSelfOfNotMem
import Theorems.Thm_GlobalTheory_QuadraticEtale_isIntegral_of_involution
import Theorems.Thm_GlobalTheory_QuadraticEtale_isUnit_or_mem_of_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.QuadraticEtale
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (σ : S →+* S)
variable [IsLocalRing R]
namespace GlobalTheory.QuadraticEtale
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x ∈ (algebraMap R S).range) (hgal : ∃ ω, IsUnit (ω - σ ω))
    {u : S} (hu : u * σ u = 1) : ∃ a, IsUnit (a + u * σ a) := by
  haveI := isIntegral_of_involution σ hσ hfix
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact ⟨0, isUnit_of_subsingleton _⟩
  obtain ⟨n, hn⟩ := Ideal.exists_maximal S
  obtain ⟨ω, hω⟩ := hgal
  by_contra hcon
  push Not at hcon
  have key : ∀ a, a + u * σ a ∈ n := by
    intro a
    have hz : σ ((a + u * σ a) * σ (a + u * σ a)) = (a + u * σ a) * σ (a + u * σ a) := by
      rw [map_mul, hσ, mul_comm]
    rcases isUnit_or_mem_of_fixed σ hfix hz with h | h
    · exact absurd (isUnit_of_mul_isUnit_left h) (hcon a)
    · have h1 : (a + u * σ a) * σ (a + u * σ a) ∈ n :=
        (Ideal.map_le_iff_le_comap (I := maximalIdeal R)).2
          (fun r hr => algebraMap_mem_of_isMaximal n hr) h
      have h2 : a + u * σ a = u * σ (a + u * σ a) := by
        rw [map_add, map_mul, hσ]
        linear_combination (-a) * hu
      rcases hn.isPrime.mem_or_mem h1 with h3 | h3
      · exact h3
      · rw [h2]; exact n.mul_mem_left _ h3
  have : ω - σ ω ∈ n := by
    have := n.sub_mem (key ω) (n.mul_mem_left (σ ω) (key 1))
    convert this using 1
    rw [map_one]; ring
  exact hn.ne_top (n.eq_top_of_isUnit_mem this hω)
end GlobalTheory.QuadraticEtale
