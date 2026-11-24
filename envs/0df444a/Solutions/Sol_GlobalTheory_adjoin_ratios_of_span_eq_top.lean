-- Prove2me | solution 1 for GlobalTheory.adjoin_ratios_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:22:16.255807+00:00
-- url     : https://prove2.me/submissions/2d2f8905-edc8-4cc1-a8ba-4d3566ba8391

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AdjoinRatiosOfSpanEqTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (R : Subalgebra K Ω) (m : ℕ) (w : Fin m → R) (k : Fin m), Ideal.span (Set.range w) = ⊤ → (w k : Ω) ≠ 0 → ∀ R' : Subalgebra K Ω, R' = Algebra.adjoin K ((R : Set Ω) ∪ Set.range fun i => (w i : Ω) / (w k : Ω)) → ∃ h : R ≤ R', (w k : Ω)⁻¹ ∈ R' ∧ (Algebra.Smooth K R → Algebra.Smooth K R') ∧ ∀ (L : Type) [Field L] [Algebra K L] (ψ : R →ₐ[K] L), ψ (w k) ≠ 0 → ∃ ψ' : R' →ₐ[K] L, ψ'.comp (Subalgebra.inclusion h) = ψ ∧ ∀ i (hi : (w i : Ω) / (w k : Ω) ∈ R'), ψ' ⟨_, hi⟩ = ψ (w i) / ψ (w k) := by
  intro K Ω _ _ _ R m w k hspan hk R' hR'
  have h : R ≤ R' := by
    rw [hR']; intro x hx; exact Algebra.subset_adjoin (Or.inl hx)
  have hrat : ∀ i, (w i : Ω) / (w k : Ω) ∈ R' := by
    intro i; rw [hR']; exact Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)
  have hinv : (w k : Ω)⁻¹ ∈ R' := by
    have h1 : (1 : R) ∈ Ideal.span (Set.range w) := by rw [hspan]; trivial
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 h1
    have h2 : ∑ i, (a i : Ω) * (w i : Ω) = 1 := by
      have := congrArg (fun x : R => (x : Ω)) ha
      simpa using this
    have h3 : (w k : Ω)⁻¹ = ∑ i, (a i : Ω) * ((w i : Ω) / (w k : Ω)) := by
      simp only [← mul_div_assoc, ← Finset.sum_div, h2, one_div]
    rw [h3]
    exact R'.sum_mem fun i _ => R'.mul_mem (h (a i).2) (hrat i)
  letI : Algebra R R' := (Subalgebra.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower K R R' := IsScalarTower.of_algebraMap_eq fun x => rfl
  have halg : ∀ x : R, ((algebraMap R R' x : R') : Ω) = x := fun x => rfl
  have hsurj : ∀ z : Ω, z ∈ R' → ∃ (n : ℕ) (a : R), z * (w k : Ω) ^ n = a := by
    intro z hz
    rw [hR'] at hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | ⟨i, rfl⟩
      · exact ⟨0, ⟨x, hx⟩, by simp⟩
      · exact ⟨1, w i, by field_simp⟩
    | algebraMap r => exact ⟨0, algebraMap K R r, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨n', b, hb⟩ := hy
      refine ⟨n + n', a * w k ^ n' + b * w k ^ n, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨n', b, hb⟩ := hy
      refine ⟨n + n', a * b, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
  haveI hloc : IsLocalization.Away (w k) R' := by
    refine IsLocalization.Away.mk (w k) ?_ ?_ ?_
    · refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ ?_
      apply Subtype.ext
      simp [halg, hk]
    · intro s
      obtain ⟨n, a, ha⟩ := hsurj s s.2
      refine ⟨n, a, Subtype.ext ?_⟩
      simpa [halg] using ha
    · intro a b hab
      refine ⟨0, ?_⟩
      have : (a : Ω) = b := by rw [← halg a, ← halg b, hab]
      rw [Subtype.ext this]
  refine ⟨h, hinv, fun hs => ?_, fun L _ _ ψ hψ => ?_⟩
  · haveI : Algebra.Smooth R R' := Algebra.Smooth.of_isLocalization_Away (w k)
    exact Algebra.Smooth.comp K R R'
  · have hu : IsUnit ((ψ : R →+* L) (w k)) := isUnit_iff_ne_zero.2 hψ
    let φ : R' →+* L := IsLocalization.Away.lift (w k) hu
    have hφ : ∀ x : R, φ (algebraMap R R' x) = ψ x := fun x =>
      IsLocalization.Away.lift_eq (w k) hu x
    refine ⟨{ φ with commutes' := fun r => ?_ }, ?_, fun i hi => ?_⟩
    · change φ (algebraMap K R' r) = _
      rw [IsScalarTower.algebraMap_apply K R R', hφ, AlgHom.commutes]
    · ext x; exact hφ x
    · change φ ⟨_, hi⟩ = _
      rw [eq_div_iff hψ, ← hφ, ← hφ, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [halg, hk]
end GlobalTheory
