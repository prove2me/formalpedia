-- Prove2me | solution 1 for GlobalTheory.UnitLemma.valsAt_torus_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:02:54.115578+00:00
-- url     : https://prove2.me/submissions/80b4f015-5324-4d53-a71b-79b0d9594492

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValsAtApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ZValuationsAtIndicesTorusSurjective
import Theorems.Thm_GlobalTheory_UnitLemma_valsAt_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
theorem _root_.solution : ∀ (G : Type) [CommGroup G] (τ : G →* G), (∀ x, τ (τ x) = x) → ∀ (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → (∀ i (n : ℤ), ∃ y : G, w i y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ i → w j y = 1) → ∀ (r : ℕ) (e : Fin r → ι), (∀ j k, e j = e k → j = k) → (∀ j k, s (e j) ≠ e k) → Function.Surjective ((valsAt w e).comp T.subtype) := by
  intro G _ τ hττ T hT ι s w hsw hex r e he hs n
  choose y hy1 hy2 using fun j : Fin r => hex (e j) (Multiplicative.toAdd n j)
  have hτ : ∀ i j, w (e i) (τ (y j)) = 1 := by
    intro i j
    have h1 : w (s (e i)) (y j) = 1 := hy2 j _ (hs i j)
    have a := (hsw (e i) (y j)).1 (by rw [h1]; simp)
    have b := (hsw (e i) (y j)⁻¹).1 (by rw [map_inv, h1]; simp)
    rw [map_inv, map_inv, toAdd_inv] at b
    apply Multiplicative.toAdd.injective
    simp only [toAdd_one]
    omega
  have hu : ∀ j, y j * (τ (y j))⁻¹ ∈ T := by
    intro j
    rw [hT, map_mul, map_inv, hττ]
    group
  refine ⟨⟨∏ j, y j * (τ (y j))⁻¹, Subgroup.prod_mem T fun j _ => hu j⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  apply Multiplicative.toAdd.injective
  funext i
  rw [valsAt_apply, map_prod, toAdd_prod]
  have hc : ∀ j, Multiplicative.toAdd (w (e i) (y j * (τ (y j))⁻¹)) = if i = j then Multiplicative.toAdd n i else 0 := by
    intro j
    rw [map_mul, map_inv, hτ, inv_one, mul_one]
    split_ifs with hij
    · subst hij; rw [hy1]; rfl
    · rw [hy2 j (e i) fun h => hij (he _ _ h)]; rfl
  simp only [hc, Finset.sum_ite_eq, Finset.mem_univ, if_true]
end GlobalTheory.UnitLemma
