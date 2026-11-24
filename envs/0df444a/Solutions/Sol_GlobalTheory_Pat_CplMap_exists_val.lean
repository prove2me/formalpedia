-- Prove2me | solution 1 for GlobalTheory.Pat.CplMap.exists_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:14:06.827368+00:00
-- url     : https://prove2.me/submissions/af917ba3-b8c0-49dd-bd69-b219bf2c31f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCplAtApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniversalLocalHom
import Theorems.Thm_GlobalTheory_Pat_CplMap_isUnit_mk
import Theorems.Thm_GlobalTheory_Pat_CplMap_map_mem_pow
import Theorems.Thm_GlobalTheory_Pat_isCplAt_approx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Pat GlobalTheory.Pat.CplMap
variable {R S S' : Type} [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S']
  {q : Ideal R} {φ : R →+* S} {ψ : R →+* S'}
variable [hq : q.IsPrime]
namespace GlobalTheory.Pat.CplMap
theorem _root_.solution (hφ : IsCplAt q φ) (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) (s : S) :
    ∃ t, IsVal q φ ψ n s t := by
  obtain ⟨a0, b0, hb0, h0⟩ := (isCplAt_approx R S q φ hφ n).1 s
  obtain ⟨u, hu⟩ := isUnit_mk hψ n hb0
  refine ⟨Ideal.Quotient.mk _ (ψ a0) * (↑u⁻¹ : S' ⧸ maximalIdeal S' ^ n), fun a b _ h => ?_⟩
  have hm : φ (b * a0 - b0 * a) ∈ maximalIdeal S ^ n := by
    have : φ (b * a0 - b0 * a) = φ b0 * (φ b * s - φ a) - φ b * (φ b0 * s - φ a0) := by
      simp only [map_sub, map_mul]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h0)
  obtain ⟨c, hc, hcq⟩ := (isCplAt_approx R S q φ hφ n).2 _ hm
  have h1 := Ideal.Quotient.eq_zero_iff_mem.mpr (map_mem_pow hψ n hcq)
  simp only [map_mul, map_sub] at h1
  have h2 := sub_eq_zero.mp ((isUnit_mk hψ n hc).mul_right_eq_zero.mp h1)
  rw [← mul_assoc, h2, ← hu, mul_right_comm, Units.mul_inv, one_mul]
end GlobalTheory.Pat.CplMap
