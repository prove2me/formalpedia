-- Prove2me | solution 1 for GlobalTheory.BCT.DimFac.finrank_fixed_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:49.663452+00:00
-- url     : https://prove2.me/submissions/81052961-5c07-4c8c-a231-470f2fc87534

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
import Theorems.Thm_GlobalTheory_BCT_DimFac_mem_fix
import Theorems.Thm_GlobalTheory_BCT_DimFac_contractLeft_map
import Theorems.Thm_GlobalTheory_BCT_DimFac_exists_split
import Theorems.Thm_GlobalTheory_BCT_DimFac_irred_right
import Theorems.Thm_GlobalTheory_BCT_DimFac_finrank_fixed_split
import Theorems.Thm_GlobalTheory_BCT_DimFac_hasComp_of_trivial
import Theorems.Thm_GlobalTheory_BCT_DimFac_HasComp_right
import Theorems.Thm_GlobalTheory_BCT_DimFac_finrank_fixed_eq_one
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_contractLeft_ne_zero
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GroundTheory.Automorphic.RestrictedTensor Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.DimFac
variable {Γ V W M : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup M] [Module ℂ M]
variable {ι : Type} {e : ι → Γ →* Γ} {L : Subgroup Γ}
namespace GlobalTheory.BCT.DimFac
theorem _root_.solution (he : ∀ i g, e i (e i g) = e i g) (hne : ∀ i j, i ≠ j → ∀ g, e i (e j g) = 1)
    (hc : ∀ i g y, Commute ((e i g)⁻¹ * g) (e i y)) (hL : ∀ g, g ∈ L ↔ ∀ i, e i g ∈ L)
    (hfin : ∀ g, {i | e i g ∉ L}.Finite) (T : Finset ι) :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V), ρ.IsIrreducible → ∀ d : ι → ℕ,
      (∀ i, HasComp ρ (e i) L (d i)) → (∀ i ∉ T, d i = 1) →
      (∃ m : V, m ≠ 0 ∧ ∀ g ∈ L, (∀ i ∈ T, e i g = 1) → ρ g m = m) → finrank ℂ (fixed ρ L) = ∏ i ∈ T, d i := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rintro V _ _ ρ hρ d h hd ⟨m, hm0, hm⟩
    exact finrank_fixed_eq_one he hne hc hL hfin hρ (fun i => hd i (by simp) ▸ h i) hm0
      (mem_fix.2 fun g hg => hm g hg (by simp))
  | insert i T hi ih =>
    rintro V _ _ ρ hρ d h hd ⟨m, hm0, hm⟩
    obtain ⟨W, _, _, σ, h1, h2, h3, ⟨f, hf0, hf⟩, h4⟩ := h i
    obtain ⟨M, _, _, τ, Φ, hτ, hΦ⟩ := exists_split hρ h1 h2 (he i) (hc i) hf0 hf
    have hirr := irred_right hρ Φ hΦ
    rw [finrank_fixed_split Φ hΦ h3 hτ fun g hg => (hL g).1 hg i, Finset.prod_insert hi, h4,
      ih M τ hirr (Function.update d i 1) ?_ ?_ ?_]
    · congr 1
      exact Finset.prod_congr rfl fun j hj => Function.update_of_ne (fun (h : j = i) => hi (h ▸ hj)) _ _
    · intro j
      by_cases hji : j = i
      · rw [hji, Function.update_self]
        exact hasComp_of_trivial hirr hτ L
      · rw [Function.update_of_ne hji]
        exact (h j).right Φ hΦ fun g => by rw [← h3, hne i j (Ne.symm hji), map_one]
    · intro j hj
      by_cases hji : j = i
      · rw [hji, Function.update_self]
      · rw [Function.update_of_ne hji]
        exact hd j (by simp [hji, hj])
    · obtain ⟨t, rfl⟩ := Φ.surjective m
      obtain ⟨l, hl⟩ := exists_contractLeft_ne_zero (z := t) (by simpa using hm0)
      refine ⟨_, hl, fun g hg hT => ?_⟩
      have h5 : e i ((e i g)⁻¹ * g) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
      have h6 := Φ.injective ((hΦ _ t).trans (hm ((e i g)⁻¹ * g) (L.mul_mem (L.inv_mem ((hL g).1 hg i)) hg)
        fun j hj => by
          rcases Finset.mem_insert.1 hj with rfl | hj
          · exact h5
          · rw [map_mul, map_inv, hne j i (fun h => hi (h ▸ hj)), hT j hj, inv_one, one_mul]))
      rw [← h3, h5, map_one, map_mul, ← map_inv (e i), hτ, one_mul] at h6
      conv_rhs => rw [← h6, contractLeft_map]
      rfl
end GlobalTheory.BCT.DimFac
