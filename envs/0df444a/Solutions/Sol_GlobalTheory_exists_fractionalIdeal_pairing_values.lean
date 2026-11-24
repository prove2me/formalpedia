-- Prove2me | solution 1 for GlobalTheory.exists_fractionalIdeal_pairing_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:48:52.06893+00:00
-- url     : https://prove2.me/submissions/9496c5f9-cf95-4373-80f6-c5f58d4a13ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeFormIdealGeneratesDualVector
import Theorems.Thm_GlobalTheory_exists_coords_of_alt_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V],
    Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) →
    ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) →
    (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), J ≠ 0 → (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v : V}, v ≠ 0 →
      ∃ K : FractionalIdeal (𝓞 F)⁰ F, K ≠ 0 ∧ ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v := by
  intro F V _ _ _ _ hV B hB L h0 hadd hsmul J hJ hLJ hJL v hv
  obtain ⟨x, hx, x', hx', hxx⟩ : ∃ x ∈ L, ∃ x' ∈ L, B x x' ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hJ
    rw [FractionalIdeal.eq_zero_iff]
    intro t ht
    have h1 := hJL t ht
    have h2 : Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w} ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro s ⟨z, hz, w, hw, rfl⟩
      simpa using hcon z hz w hw
    simpa using h2 h1
  obtain ⟨c, c', rfl⟩ := exists_coords_of_alt_ne_zero hV B hB hxx v
  let M : Submodule (𝓞 F) F :=
    { carrier := {t | ∃ z ∈ L, t = B z (c • x + c' • x')}
      zero_mem' := ⟨0, h0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
        exact ⟨z + w, hadd z hz w hw, by rw [map_add B, LinearMap.add_apply]⟩
      smul_mem' := by
        rintro a _ ⟨z, hz, rfl⟩
        refine ⟨(a : F) • z, hsmul a z hz, ?_⟩
        rw [map_smul B, LinearMap.smul_apply, Algebra.smul_def, smul_eq_mul] }
  have hM : M ≤ ((FractionalIdeal.spanSingleton (𝓞 F)⁰ c * J +
      FractionalIdeal.spanSingleton (𝓞 F)⁰ c' * J : FractionalIdeal (𝓞 F)⁰ F) :
      Submodule (𝓞 F) F) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [FractionalIdeal.coe_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    refine Submodule.add_mem_sup ?_ ?_
    · exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
        (hLJ z hz x hx)
    · exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
        (hLJ z hz x' hx')
  refine ⟨⟨M, FractionalIdeal.isFractional_of_le hM⟩, ?_, fun t => Iff.rfl⟩
  intro hK0
  have hK := FractionalIdeal.eq_zero_iff.1 hK0
  have h1 := hK _ (show B x (c • x + c' • x') ∈ M from ⟨x, hx, rfl⟩)
  have h2 := hK _ (show B x' (c • x + c' • x') ∈ M from ⟨x', hx', rfl⟩)
  have hanti : B x' x = - B x x' := by
    have h1 := hB (x + x')
    simp only [map_add, LinearMap.add_apply, hB] at h1
    linear_combination h1
  simp [hB, hanti, hxx] at h1 h2
  apply hv
  simp [h1, h2]
end GlobalTheory
