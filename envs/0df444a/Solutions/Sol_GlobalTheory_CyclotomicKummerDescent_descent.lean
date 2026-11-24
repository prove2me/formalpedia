-- Prove2me | solution 1 for GlobalTheory.CyclotomicKummerDescent.descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:08:17.987799+00:00
-- url     : https://prove2.me/submissions/23e84db4-7af7-4545-9b17-522a5004aadd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowDescentCyclotomic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open GlobalTheory.CyclotomicKummerDescent
namespace GlobalTheory.CyclotomicKummerDescent
theorem _root_.solution {E K : Type} [Field E] [Field K] [Algebra E K] {M : ℕ}
    [NeZero M] [IsCyclotomicExtension {M} E K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) {k n : ℕ}
    (τ : K ≃ₐ[E] K) (hτ : τ ζ = ζ ^ (k + 1))
    (hN : M ∣ (∑ i ∈ Finset.range n, (k + 1) ^ i) * k) {u : E} {w : K} (hw0 : w ≠ 0)
    (hw : w ^ M = algebraMap E K u) :
    ∃ (α : K) (v : E), α ^ M = 1 ∧ α ^ (∑ i ∈ Finset.range n, (k + 1) ^ i) = 1 ∧
      algebraMap E K v * α = w ^ k := by
  haveI := IsCyclotomicExtension.finiteDimensional {M} E K
  haveI := IsCyclotomicExtension.isGalois {M} E K
  have hext : ∀ σ σ' : K ≃ₐ[E] K, σ ζ = σ' ζ → σ = σ' := by
    intro σ σ' h
    apply hζ.autToPow_injective E
    rw [← hζ.autToPow_spec E σ, ← hζ.autToPow_spec E σ'] at h
    exact Units.ext (ZMod.val_injective M (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  have hcomm : ∀ σ : K ≃ₐ[E] K, σ * τ = τ * σ := fun σ =>
    hζ.autToPow_injective E (by rw [map_mul, map_mul, mul_comm])
  have hroot : ∀ η : K, η ^ M = 1 → τ η = η ^ (k + 1) := by
    intro η hη
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
    rw [map_pow, hτ, ← pow_mul, ← pow_mul, mul_comm]
  have hcoc : ∀ σ : K ≃ₐ[E] K, ∃ a : K, a ^ M = 1 ∧ σ w = a * w := by
    intro σ
    refine ⟨σ w / w, ?_, by field_simp⟩
    rw [div_pow, ← map_pow, hw, AlgEquiv.commutes, ← hw, div_self (pow_ne_zero _ hw0)]
  have hne : ∀ a : K, a ^ M = 1 → a ≠ 0 := by
    rintro a ha rfl
    rw [zero_pow (NeZero.ne M)] at ha
    exact zero_ne_one ha
  obtain ⟨α, hαM, hα⟩ := hcoc τ
  have hα0 := hne α hαM
  have hiter : ∀ m : ℕ, (τ ^ m) w = α ^ (∑ i ∈ Finset.range m, (k + 1) ^ i) * w ∧
      (τ ^ m) ζ = ζ ^ ((k + 1) ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih.1, ih.2, map_mul, map_pow,
        map_pow, hτ, hα, hroot α hαM, geom_sum_succ]
      constructor <;> ring
  have hgeom : ∀ m : ℕ, (k + 1) ^ m = (∑ i ∈ Finset.range m, (k + 1) ^ i) * k + 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, pow_succ, add_mul, mul_add, mul_one]; omega
  have hτn : τ ^ n = 1 := by
    apply hext
    obtain ⟨c, hc⟩ := hN
    rw [(hiter n).2, hgeom, hc, pow_succ, pow_mul, hζ.pow_eq_one]
    simp
  have hαN : α ^ (∑ i ∈ Finset.range n, (k + 1) ^ i) = 1 := by
    have h := (hiter n).1
    rw [hτn, AlgEquiv.one_apply] at h
    exact mul_right_cancel₀ hw0 (by rw [← h, one_mul])
  have hfix : ∀ σ : K ≃ₐ[E] K, σ (w ^ k / α) = w ^ k / α := by
    intro σ
    obtain ⟨a, haM, ha⟩ := hcoc σ
    have ha0 := hne a haM
    have h := congrArg (fun f : K ≃ₐ[E] K => f w) (hcomm σ)
    simp only [AlgEquiv.mul_apply] at h
    rw [hα, ha, map_mul, map_mul, ha, hα, hroot a haM] at h
    have hσα : σ α = a ^ k * α :=
      mul_right_cancel₀ (mul_ne_zero ha0 hw0) (by rw [h]; ring)
    rw [map_div₀, map_pow, hσα, ha, mul_pow]
    field_simp
  obtain ⟨v, hv⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfix
  exact ⟨α, v, hαM, hαN, by rw [hv]; field_simp⟩
end GlobalTheory.CyclotomicKummerDescent
