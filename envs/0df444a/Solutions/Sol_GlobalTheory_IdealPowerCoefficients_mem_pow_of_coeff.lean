-- Prove2me | solution 1 for GlobalTheory.IdealPowerCoefficients.mem_pow_of_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:09:46.663194+00:00
-- url     : https://prove2.me/submissions/21f5e683-2de8-4d49-af2f-64f42cfc1710

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemPowIffCoeffMem
import Theorems.Thm_GlobalTheory_IdealPowerCoefficients_coeff_cof
import Theorems.Thm_GlobalTheory_IdealPowerCoefficients_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IdealPowerCoefficients
open MvPowerSeries Finsupp
variable {R : Type u_1} [CommRing R] {κ : Type u_2}
namespace GlobalTheory.IdealPowerCoefficients
theorem _root_.solution [Finite κ] (I : Ideal R) (n : ℕ) (f : MvPowerSeries κ R)
    (hf : ∀ e : κ →₀ ℕ, coeff e f ∈ I ^ (n - e.degree)) :
    f ∈ (Ideal.map C I ⊔ Ideal.span (Set.range X)) ^ n := by
  classical
  have := Fintype.ofFinite κ
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [decomp f]
    refine Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun k _ => ?_)
    · have h0 := hf 0
      rw [map_zero, tsub_zero] at h0
      have h1 : C (coeff 0 f) ∈ Ideal.map (C : R →+* MvPowerSeries κ R) (I ^ (n + 1)) :=
        Ideal.mem_map_of_mem _ h0
      rw [Ideal.map_pow] at h1
      exact Ideal.pow_right_mono le_sup_left _ h1
    · rw [pow_succ']
      refine Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)) (ih _ fun e => ?_)
      rw [coeff_cof]
      split_ifs
      · have h2 := hf (e + single k 1)
        rw [map_add, degree_single] at h2
        have h3 : n + 1 - (e.degree + 1) = n - e.degree := by omega
        rwa [h3] at h2
      · exact Ideal.zero_mem _
end GlobalTheory.IdealPowerCoefficients
