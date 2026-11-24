-- Prove2me | solution 1 for GlobalTheory.LocalFlatMax.relationsLift_of_lTensor_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:49:01.085308+00:00
-- url     : https://prove2.me/submissions/f05dd860-37a9-4754-b8b1-26da856bb1b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingHomFlatOfCompFlatOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_LocalFlat_range_lTensor_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap IsLocalRing
open GlobalTheory
open GlobalTheory.LocalFlatMax
universe u
variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
namespace GlobalTheory.LocalFlatMax
theorem _root_.solution (K : Ideal A)
    (h : ∀ L : Ideal A, K ≤ L → Function.Injective (L.subtype.lTensor M)) :
    LocalFlat.RelationsLift K M := by
  intro F _ _ f x hx
  have hy : ∃ y : M ⊗[A] K, TensorProduct.rid A M (K.subtype.lTensor M y) =
      TensorProduct.rid A M (f.lTensor M x) := by
    refine Submodule.smul_induction_on (p := fun d => ∃ y : M ⊗[A] K,
      TensorProduct.rid A M (K.subtype.lTensor M y) = d) hx ?_ ?_
    · intro r hr m _
      exact ⟨m ⊗ₜ ⟨r, hr⟩, by simp⟩
    · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, by simp⟩
  obtain ⟨y, hy⟩ := hy
  replace hy := (TensorProduct.rid A M).injective hy
  let g : F × K →ₗ[A] A := f.coprod (-K.subtype)
  let z : M ⊗[A] (F × K) := (inl A F K).lTensor M x + (inr A F K).lTensor M y
  have hgz : g.lTensor M z = 0 := by
    simp only [z, g, map_add, ← lTensor_comp_apply, coprod_inl, coprod_inr, lTensor_neg,
      LinearMap.neg_apply, hy, add_neg_cancel]
  have hL : K ≤ range g := fun a ha => ⟨(0, ⟨-a, neg_mem ha⟩), by simp [g]⟩
  have hz : g.rangeRestrict.lTensor M z = 0 := by
    apply h _ hL
    rw [← lTensor_comp_apply, map_zero]
    exact hgz
  obtain ⟨w, hw⟩ := (lTensor_exact M (exact_subtype_ker_map g.rangeRestrict)
    g.surjective_rangeRestrict z).mp hz
  refine LocalFlat.range_lTensor_le (fst A F K ∘ₗ (ker g.rangeRestrict).subtype) _ ?_ ⟨w, ?_⟩
  · rintro ⟨⟨v, k⟩, hv⟩
    have : f v + -(k : A) = 0 := congrArg Subtype.val hv
    change f v ∈ K
    rw [add_neg_eq_zero.mp this]
    exact k.2
  · rw [lTensor_comp_apply, hw]
    simp only [z, map_add, ← lTensor_comp_apply, fst_comp_inl, fst_comp_inr, lTensor_id,
      lTensor_zero, LinearMap.zero_apply, add_zero, id_apply]
end GlobalTheory.LocalFlatMax
