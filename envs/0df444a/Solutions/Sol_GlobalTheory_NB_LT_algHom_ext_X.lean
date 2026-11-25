-- Prove2me | solution 1 for GlobalTheory.NB.LT.algHom_ext_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:50.460675+00:00
-- url     : https://prove2.me/submissions/31986952-d06b-4ab7-8dad-ef65d826ed9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdSubOfDvdSubX
import Theorems.Thm_GlobalTheory_NB_LT_algHom_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open PowerSeries
namespace GlobalTheory.NB.LT
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}
open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
private lemma X_pow_dvd_sub_aeval_trunc (ρ : R⟦X⟧ →ₐ[R] R⟦X⟧) (hρ : X ∣ ρ X) (n : ℕ)
    (f : R⟦X⟧) : X ^ n ∣ ρ f - Polynomial.aeval (ρ X) (trunc n f) := by
  obtain ⟨g, hg⟩ : X ^ n ∣ f - (trunc n f : R⟦X⟧) := by
    rw [X_pow_dvd_iff]
    intro m hm
    simp [coeff_trunc, hm]
  have e : ρ f - Polynomial.aeval (ρ X) (trunc n f) = ρ (X ^ n) * ρ g := by
    rw [← _root_.GlobalTheory.NB.LT.algHom_coe ρ, ← map_sub, hg, map_mul]
  rw [e, map_pow]
  exact (pow_dvd_pow_of_dvd hρ n).mul_right _
end GlobalTheory.NB.LT
end
end

set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB GlobalTheory.NB.LT
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}
open PowerSeries
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}
namespace GlobalTheory.NB.LT
namespace _root_.GlobalTheory.NB.LT
theorem _root_.solution (σ τ : R⟦X⟧ →ₐ[R] R⟦X⟧) (h : σ X = τ X) (hX : X ∣ σ X) : σ = τ := by
  refine AlgHom.ext fun f => PowerSeries.ext fun m => ?_
  have h1 := X_pow_dvd_sub_aeval_trunc σ hX (m + 1) f
  have h2 := X_pow_dvd_sub_aeval_trunc τ (h ▸ hX) (m + 1) f
  rw [h] at h1
  have h3 := dvd_sub h1 h2
  rw [sub_sub_sub_cancel_right] at h3
  have := (X_pow_dvd_iff.mp h3) m (Nat.lt_succ_self m)
  rwa [map_sub, sub_eq_zero] at this
end _root_.GlobalTheory.NB.LT
end GlobalTheory.NB.LT
