-- Prove2me | solution 1 for GlobalTheory.NormFormGauss.gauss_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:46:32.804916+00:00
-- url     : https://prove2.me/submissions/11eddd0e-9aac-452e-88fd-20684412cb75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Theorems.Thm_GlobalTheory_NormFormGauss_gauss_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.NormFormGauss
namespace GlobalTheory.NormFormGauss
theorem _root_.solution : ∀ {R : Type} [CommRing R] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r ∈ P, σ r ∈ P) → (∃ r, σ r - r ∉ P) → ∀ χ : R → ℂ, (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 → (∀ r ∈ P, χ r = 1) → (∀ t, χ (σ t) = χ t) → (∃ t, χ t ≠ 1) → (∑ᶠ q : R ⧸ P, χ (w * (Quotient.out q : R) * σ (Quotient.out q : R))) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) := by
  intro R _ σ w hσ hw P hP hfin hst ⟨r, hr⟩ χ hadd h0 hχP hχσ ⟨t, ht⟩
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  let s : R ⧸ P →+* R ⧸ P := Ideal.quotientMap P σ (fun r hr => hst r hr)
  have hs : ∀ x, s (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (σ x) := fun x => rfl
  have hout : ∀ q : R ⧸ P, Ideal.Quotient.mk P (Quotient.out q) = q := fun q => Quotient.out_eq q
  have hcongr : ∀ a b : R, Ideal.Quotient.mk P a = Ideal.Quotient.mk P b → χ a = χ b := by
    intro a b h
    have h1 := hχP _ (Ideal.Quotient.eq.1 h)
    have h2 := hadd (a - b) b
    rw [h1, one_mul, sub_add_cancel] at h2
    exact h2
  let f : R ⧸ P → ℂ := fun q => χ (w * Quotient.out q)
  have hf : ∀ a : R, f (Ideal.Quotient.mk P a) = χ (w * a) := fun a =>
    hcongr _ _ (by rw [map_mul, map_mul, hout])
  have key := gauss_field s
    (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hs, hs, hσ])
    (Ideal.Quotient.mk P r)
    (by
      rw [hs, ← map_sub]
      exact fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h))
    f
    (fun a b => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [← map_add, hf, hf, hf, mul_add, hadd])
    (by rw [← map_zero (Ideal.Quotient.mk P), hf, mul_zero, h0])
    (Ideal.Quotient.mk P (t + σ t))
    (by rw [hs, map_add σ, hσ, add_comm])
    (by
      rw [hf, mul_add, hadd, ← hχσ (w * σ t), map_mul, hσ, ← hadd, ← add_mul, hw, one_mul]
      exact ht)
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, ← key]
  refine Finset.sum_congr rfl fun q _ => ?_
  conv_rhs => rw [← hout q]
  rw [hs, ← map_mul, hf, mul_assoc]
end GlobalTheory.NormFormGauss
