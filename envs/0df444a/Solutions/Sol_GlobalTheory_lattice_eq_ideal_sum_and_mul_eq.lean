-- Prove2me | solution 1 for GlobalTheory.lattice_eq_ideal_sum_and_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:44.828855+00:00
-- url     : https://prove2.me/submissions/a2e8f12c-966f-4ab1-8d23-ec92bfc3d6d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeFormIdealPairOfVectors
import Theorems.Thm_GlobalTheory_exists_coords_of_alt_pair

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
    ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) → ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v w : V}, v ≠ 0 → ∀ (I K : FractionalIdeal (𝓞 F)⁰ F), (∀ a : F, a ∈ I ↔ a • v ∈ L) →
    (∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) → B w v = 1 → (∀ t ∈ K, t • w ∈ L) →
    (∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w) ∧ I * K = J := by
  intro F V _ _ _ _ hV B hB L _ hadd hsmul J hJ hJs v w hv I K hI hK hw hwL
  have hvw : B v w = -1 := by
    have h := hB (v + w)
    simp only [map_add, LinearMap.add_apply, hB, hw] at h
    linear_combination h
  have hmem : ∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w := by
    intro x
    constructor
    · intro hx
      obtain ⟨p, q, rfl⟩ := exists_coords_of_alt_pair hV B hB hv hw x
      have hq : q ∈ K := (hK q).2 ⟨_, hx, by simp [hB, hw]⟩
      refine ⟨p, (hI p).2 ?_, q, hq, rfl⟩
      have h1 := hadd _ hx _ (hsmul (-1) _ (hwL q hq))
      simpa using h1
    · rintro ⟨a, ha, t, ht, rfl⟩
      exact hadd _ ((hI a).1 ha) _ (hwL t ht)
  refine ⟨hmem, le_antisymm ?_ ?_⟩
  · rw [FractionalIdeal.mul_le]
    intro a ha t ht
    have h := hJ _ (hwL t ht) _ ((hI a).1 ha)
    simpa [hw, mul_comm] using h
  · intro t ht
    have h := hJs t ht
    have hle : Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}
        ≤ ((I * K : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) := by
      rw [Submodule.span_le]
      rintro _ ⟨z, hz, z', hz', rfl⟩
      obtain ⟨a, ha, s, hs, rfl⟩ := (hmem z).1 hz
      obtain ⟨a', ha', s', hs', rfl⟩ := (hmem z').1 hz'
      have e : B (a • v + s • w) (a' • v + s' • w) = a' * s - a * s' := by
        simp [hB, hw, hvw]; ring
      rw [e]
      exact Submodule.sub_mem _ (FractionalIdeal.mul_mem_mul ha' hs)
        (FractionalIdeal.mul_mem_mul ha hs')
    exact hle h
end GlobalTheory
