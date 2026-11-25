-- Prove2me | solution 1 for GlobalTheory.adicCompletion_valuation_map_uniformiser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:27.033903+00:00
-- url     : https://prove2.me/submissions/54bf7e8b-0295-4585-b1cc-2689e435821d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AdicCompletionValuationMapUniformiser

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel NumberField IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → ∀ ϖ : 𝒪[k], Irreducible ϖ → Valued.v (φ (ϖ : k)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  intro F _ _ v k _ _ _ _ φ hφ ϖ hϖ

  have hnu : ∀ c : 𝒪[k], Valued.v (φ (c : k)) < 1 → ¬ IsUnit c := by
    intro c hc hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have hw' : φ (c : k) * φ (w : k) = 1 := by
      rw [← map_mul, ← map_one φ]
      congr 1
      exact_mod_cast congrArg (fun t : 𝒪[k] => (t : k)) hw
    have h1 : Valued.v (φ (c : k)) * Valued.v (φ (w : k)) = 1 := by
      rw [← map_mul, hw', map_one]
    have h2 : Valued.v (φ (w : k)) ≤ 1 := (hφ _).2 w.2
    have h3 : Valued.v (φ (c : k)) * Valued.v (φ (w : k)) ≤ Valued.v (φ (c : k)) * 1 :=
      by gcongr
    rw [h1, mul_one] at h3
    exact absurd hc (not_lt.2 h3)
  set x := φ (ϖ : k) with hxdef
  have hϖ0 : (ϖ : k) ≠ 0 := by
    intro h; exact hϖ.ne_zero (Subtype.ext h)
  have hx0 : x ≠ 0 := by
    simpa [hxdef] using hϖ0
  have hvx0 : Valued.v x ≠ 0 := by
    simpa using hx0
  have hvx1 : Valued.v x < 1 := by
    have hle : Valued.v x ≤ 1 := (hφ _).2 ϖ.2
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hϖ.not_isUnit
    have hinv : ((ϖ : k))⁻¹ ∈ 𝒪[k] := by
      refine (hφ _).1 ?_
      rw [map_inv₀, map_inv₀, ← hxdef, heq, inv_one]
    refine IsUnit.of_mul_eq_one (b := (⟨_, hinv⟩ : 𝒪[k])) ?_
    apply Subtype.ext
    simp [mul_inv_cancel₀ hϖ0]
  obtain ⟨π₀, hπ₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  have hlt1 : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.coe_one, WithZero.coe_lt_coe]
    show (-1 : ℤ) < 0
    norm_num
  have hvπ0 : Valued.v π₀ ≠ 0 := by rw [hπ₀]; exact WithZero.coe_ne_zero
  have hπ0 : π₀ ≠ 0 := by
    intro h; apply hvπ0; rw [h, map_zero]
  set a := φ.symm π₀ with hadef
  have hφa : φ a = π₀ := by simp [hadef]
  have ha0 : a ≠ 0 := by
    intro h; apply hπ0; rw [← hφa, h, map_zero]
  have ha : a ∈ 𝒪[k] := (hφ a).1 (by rw [hφa, hπ₀]; exact hlt1.le)
  apply le_antisymm
  · obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 hvx0
    rw [← hm] at hvx1 ⊢
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at hvx1
    rw [WithZero.coe_le_coe]
    have h1 : Multiplicative.toAdd m < 0 := hvx1
    show Multiplicative.toAdd m ≤ -1
    omega
  · by_contra hcon
    rw [not_le] at hcon
    set b := (ϖ : k) / a with hbdef
    have hφb : Valued.v (φ b) < 1 := by
      rw [hbdef, map_div₀, hφa, map_div₀, ← hxdef, div_lt_one₀ (pos_iff_ne_zero.2 hvπ0), hπ₀]
      exact hcon
    have hb : b ∈ 𝒪[k] := (hφ b).1 hφb.le
    have hprod : ϖ = (⟨a, ha⟩ : 𝒪[k]) * ⟨b, hb⟩ := by
      apply Subtype.ext
      show (ϖ : k) = a * ((ϖ : k) / a)
      rw [mul_div_cancel₀ _ ha0]
    rcases hϖ.isUnit_or_isUnit hprod with h | h
    · exact hnu ⟨a, ha⟩ (by rw [hφa, hπ₀]; exact hlt1) h
    · exact hnu ⟨b, hb⟩ hφb h
end GlobalTheory
