-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.exists_split_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:15:57.838894+00:00
-- url     : https://prove2.me/submissions/9bebea5f-8f8c-4c9f-a1f6-250fe180f17e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
namespace GlobalTheory.HeckeCompare
theorem _root_.solution {O : Type} [CommRing O] [IsDedekindDomain O] {p : O} (hp : p ≠ 0) (P P' : Ideal O)
    [hP : P.IsMaximal] [hP' : P'.IsMaximal] (hco : P ⊔ P' = ⊤) : ∃ (m n : ℕ) (w u v a : O), w + v + u = 1 ∧
      a ∉ P ∧ a ∉ P' ∧ p ∣ w * a ∧ (∀ b ∈ P ^ m, p ∣ u * b) ∧ ∀ b ∈ P' ^ n, p ∣ v * b := by
  obtain ⟨J, hJ, e⟩ := Ideal.eq_prime_pow_mul_coprime (I := Ideal.span {p}) (by simpa using hp) P
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    simp [hp] at e
  obtain ⟨R, hR, e'⟩ := Ideal.eq_prime_pow_mul_coprime hJ0 P'
  obtain ⟨m, e⟩ : ∃ m, Ideal.span {p} = P ^ m * J := ⟨_, e⟩
  obtain ⟨n, e'⟩ : ∃ n, J = P' ^ n * R := ⟨_, e'⟩
  have h₁ : IsCoprime P R := (Ideal.isCoprime_iff_sup_eq.2 hJ).of_isCoprime_of_dvd_right ⟨P' ^ n, by rw [e', mul_comm]⟩
  have h₂ : IsCoprime P' R := Ideal.isCoprime_iff_sup_eq.2 hR
  have h₃ : IsCoprime (P ^ (m + 1) * P' ^ (n + 1)) R :=
    IsCoprime.mul_left (IsCoprime.pow_left h₁) (IsCoprime.pow_left h₂)
  have h₄ : IsCoprime (P ^ m) (P' ^ n) := (Ideal.isCoprime_iff_sup_eq.2 hco).pow
  obtain ⟨w, hw, a, ha, hwa⟩ := Ideal.isCoprime_iff_exists.1 h₃
  obtain ⟨s, hs, t, ht, hst⟩ := Ideal.isCoprime_iff_exists.1 h₄
  have key : ∀ x ∈ P ^ m, ∀ y ∈ P' ^ n, p ∣ x * (y * a) := fun x hx y hy => by
    rw [← Ideal.mem_span_singleton, e, e']
    exact Ideal.mul_mem_mul hx (Ideal.mul_mem_mul hy ha)
  have hn : ∀ I : Ideal O, I.IsMaximal → w ∈ I → a ∉ I := fun I hI h h' =>
    hI.ne_top ((Ideal.eq_top_iff_one _).2 (hwa ▸ I.add_mem h h'))
  refine ⟨m, n, w, a * t, a * s, a, by linear_combination hwa + a * hst,
    hn _ hP (Ideal.pow_le_self (Nat.succ_ne_zero m) (Ideal.mul_le_inf hw).1),
    hn _ hP' (Ideal.pow_le_self (Nat.succ_ne_zero n) (Ideal.mul_le_inf hw).2), ?_, fun b hb => ?_, fun b hb => ?_⟩
  · rw [← Ideal.mem_span_singleton, e, e', ← mul_assoc]
    exact Ideal.mul_mem_mul (Ideal.mul_mono (Ideal.pow_le_pow_right (Nat.le_succ m))
      (Ideal.pow_le_pow_right (Nat.le_succ n)) hw) ha
  · rw [show a * t * b = b * (t * a) by ring]; exact key b hb t ht
  · rw [show a * s * b = s * (b * a) by ring]; exact key s hs b hb
end GlobalTheory.HeckeCompare
