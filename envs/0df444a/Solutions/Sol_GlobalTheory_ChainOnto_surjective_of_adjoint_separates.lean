-- Prove2me | solution 1 for GlobalTheory.ChainOnto.surjective_of_adjoint_separates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:28.42339+00:00
-- url     : https://prove2.me/submissions/81c23783-f5fe-48d4-960e-155ad0aded7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SurjectiveOfAdjointSeparatesLabelledParts
import Theorems.Thm_GlobalTheory_ChainOnto_exists_sum_pairwise_unrelated
import Theorems.Thm_GlobalTheory_ChainOnto_exists_ne_zero_orth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.ChainOnto
namespace GlobalTheory.ChainOnto
theorem _root_.solution : ∀ (A C I J : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ A] (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (Θ : C →ₗ[ℂ] A) (pA : A → I → Prop) (pC : C → J → Prop) (RA : I → I → Prop) (RC : J → J → Prop) (T : I → J), (∀ x y, ipA x y = conj (ipA y x)) → (∀ x, x ≠ 0 → 0 < (ipA x x).re) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → Equivalence RA → Submodule.span ℂ {u | ∃ B, pA u B} = ⊤ → (∀ u u' B B' (a : ℂ), pA u B → pA u' B' → RA B B' → u + a • u' ≠ 0 → pA (u + a • u') B) → (∀ u B (a : ℂ), pA u B → a ≠ 0 → pA (a • u) B) → (∀ B B', RC (T B) (T B') → RA B B') → (∀ (ι : Type) (x : ι → C) (B : ι → J), (∀ i, pC (x i) (B i)) → (∀ i i', i ≠ i' → ¬ RC (B i) (B i')) → LinearIndependent ℂ x) → (∀ u B, pA u B → ∃ x, (∀ y, ip y x = ipA (Θ y) u) ∧ pC x (T B)) → Function.Surjective Θ := by
  intro A C I J _ _ _ _ _ ipA ip Θ pA pC RA RC T hsym _ hpos hRA hspan hmerge hsmul hRCA hli hex
  classical
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨u, hu0, horth⟩ := exists_ne_zero_orth ipA hsym _ hne
  have horth' : ∀ y, ipA (Θ y) u = 0 := fun y => horth _ (LinearMap.mem_range_self Θ y)
  obtain ⟨s, v, hv, hp, hus⟩ := exists_sum_pairwise_unrelated pA RA hRA hmerge hsmul u
    (by rw [hspan]; exact Submodule.mem_top)
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hu0 (by simpa using hus)
  have hx : ∀ i : s, ∃ x, (∀ y, ip y x = ipA (Θ y) (v i)) ∧ pC x (T i) :=
    fun i => hex _ _ (hv i i.2)
  choose x hx1 hx2 using hx
  have hlin := hli s x (fun i => T i) hx2
    (fun i i' hne hR => hp i i.2 i' i'.2 (fun h => hne (Subtype.ext h)) (hRCA _ _ hR))
  have hzy : ∀ y, ip y (∑ i, x i) = 0 := by
    intro y
    rw [map_sum]
    simp_rw [hx1]
    rw [← map_sum, Finset.sum_coe_sort s v, ← hus, horth']
  have hz : ∑ i, x i = 0 := by
    by_contra h
    have := hpos _ h
    rw [hzy] at this
    simp at this
  obtain ⟨i, hi⟩ := hs
  have := Fintype.linearIndependent_iff.mp hlin (fun _ => 1) (by simpa using hz) ⟨i, hi⟩
  exact one_ne_zero this
end GlobalTheory.ChainOnto
