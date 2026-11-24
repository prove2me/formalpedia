-- Prove2me | solution 1 for GlobalTheory.DoubleCosetEuler.doubleCoset_mk_eq_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:25:04.458108+00:00
-- url     : https://prove2.me/submissions/4438c395-7f6c-475c-b198-b380ce034504

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumDoubleCosetEqFinprodLocalSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open scoped Classical
open GlobalTheory GlobalTheory.DoubleCosetEuler
namespace GlobalTheory.DoubleCosetEuler
theorem _root_.solution (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (T K : Subgroup G) (TH KH : ∀ i, Subgroup (H i)) (S0 : Finset ι)
    (hsurj : ∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) (hT : ∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i)
    (g g' : G) (hg : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g = t * k)
    (hg' : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g' = t * k)
    (h : ∀ i ∈ S0, DoubleCoset.mk (TH i) (KH i) (p i g) = DoubleCoset.mk (TH i) (KH i) (p i g')) :
    DoubleCoset.mk T K g = DoubleCoset.mk T K g' := by
  have hloc : ∀ i, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g' = t * p i g * k ∧
      (p i g ∈ KH i → p i g' ∈ KH i → t = 1) := by
    intro i
    by_cases hk : p i g ∈ KH i ∧ p i g' ∈ KH i
    · exact ⟨1, (TH i).one_mem, (p i g)⁻¹ * p i g', mul_mem (inv_mem hk.1) hk.2, by group,
        fun _ _ => rfl⟩
    · by_cases hi : i ∈ S0
      · obtain ⟨t, ht, k, hk', he⟩ := (DoubleCoset.eq _ _ _ _).1 (h i hi)
        exact ⟨t, ht, k, hk', he, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
      · obtain ⟨a, ha, b, hb, hab⟩ := hg i hi
        obtain ⟨a', ha', b', hb', hab'⟩ := hg' i hi
        refine ⟨a' * a⁻¹, mul_mem ha' (inv_mem ha), b⁻¹ * b', mul_mem (inv_mem hb) hb', ?_,
          fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
        rw [hab, hab']; group
  choose t ht k hk he h1 using hloc
  obtain ⟨x, hx⟩ := hsurj t (by
    filter_upwards [hcof g, hcof g'] with i hi hi'
    rw [h1 i hi hi']; exact (KH i).one_mem)
  rw [DoubleCoset.eq]
  refine ⟨x, (hT x).2 (fun i => by rw [hx]; exact ht i), g⁻¹ * x⁻¹ * g', (hK _).2 (fun i => ?_), by group⟩
  rw [map_mul, map_mul, map_inv, map_inv, hx, he i]
  convert hk i using 1
  group
end GlobalTheory.DoubleCosetEuler
