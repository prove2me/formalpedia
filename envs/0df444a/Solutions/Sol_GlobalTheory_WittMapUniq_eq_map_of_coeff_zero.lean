-- Prove2me | solution 1 for GlobalTheory.WittMapUniq.eq_map_of_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:28:11.291902+00:00
-- url     : https://prove2.me/submissions/d40942fe-b49f-493a-ad78-b0c2fc870ecd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorRingHomEqMapOfCoeffZero
import Theorems.Thm_GlobalTheory_WittMapUniq_exists_pow_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory GlobalTheory.WittMapUniq
open WittVector
namespace GlobalTheory.WittMapUniq
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l]
    [PerfectRing R l] [CommRing O] [CharP O l] [PerfectRing O l]
    (F : WittVector l R →+* WittVector l O) (ψ : R →+* O),
    (∀ a, (F a).coeff 0 = ψ (a.coeff 0)) → F = WittVector.map ψ := by
  intro l _ R O _ _ _ _ _ _ F ψ hF
  have hdiff : ∀ x : WittVector l R, (l : WittVector l O) ∣ F x - WittVector.map ψ x := by
    intro x
    rw [← Ideal.mem_span_singleton, mem_span_p_iff_coeff_zero_eq_zero]
    have h := (WittVector.constantCoeff : WittVector l O →+* O).map_sub (F x) (WittVector.map ψ x)
    simp only [WittVector.constantCoeff_apply] at h
    rw [h, hF, WittVector.map_coeff, sub_self]
  have hteich : ∀ (n : ℕ) (r : R),
      (l : WittVector l O) ^ (n + 1) ∣ F (teichmuller l r) - teichmuller l (ψ r) := by
    intro n r
    obtain ⟨s, rfl⟩ := exists_pow_pow_eq l R n r
    have h1 : (l : WittVector l O) ∣ F (teichmuller l s) - teichmuller l (ψ s) := by
      have := hdiff (teichmuller l s)
      rwa [WittVector.map_teichmuller] at this
    have h2 := dvd_sub_pow_of_dvd_sub h1 n
    rw [map_pow, map_pow, map_pow, map_pow]
    exact h2
  ext x m
  have key : ∀ n : ℕ, F x - WittVector.map ψ x ∈ Ideal.span {((l : WittVector l O) ^ n)} := by
    intro n
    let I : Ideal (WittVector l O) := Ideal.span {((l : WittVector l O) ^ n)}
    have hfg : (Ideal.Quotient.mk I).comp F = (Ideal.Quotient.mk I).comp (WittVector.map ψ) := by
      refine WittVector.eq_of_apply_teichmuller_eq _ _ ⟨n, ?_⟩ ?_
      · rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
      · intro r
        simp only [RingHom.comp_apply, WittVector.map_teichmuller]
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
        exact dvd_trans (pow_dvd_pow _ n.le_succ) (hteich n r)
    have := congrArg (fun f => f x) hfg
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.mp this
  have h := (mem_span_p_pow_iff_le_coeff_eq_zero _ (m + 1)).mp (key (m + 1))
  have h' := (le_coeff_eq_iff_le_sub_coeff_eq_zero (n := m + 1)).mpr h
  exact h' m (Nat.lt_succ_self m)
end GlobalTheory.WittMapUniq
