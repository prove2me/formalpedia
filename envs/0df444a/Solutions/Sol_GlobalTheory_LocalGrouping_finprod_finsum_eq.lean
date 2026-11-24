-- Prove2me | solution 1 for GlobalTheory.LocalGrouping.finprod_finsum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:49:02.024741+00:00
-- url     : https://prove2.me/submissions/565e599b-f7cb-4032-b186-1a747736875e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumRestrictedProductCount

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
open GlobalTheory GlobalTheory.LocalGrouping
open Function
namespace GlobalTheory.LocalGrouping
theorem _root_.solution (I : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ)
    (T : Finset I) (u : ∀ i, D i) (hTS : (T : Set I) ⊆ S)
    (hfin : ∀ i ∈ S, (support (B i)).Finite)
    (hind : ∀ i ∈ S, i ∉ T → ∀ d, B i d = if d = u i then 1 else 0) :
    ∏ᶠ i ∈ S, ∑ᶠ d, B i d = ∑ᶠ f : (∀ i : T, D i), ∏ i : T, B i (f i) := by
  have hone : ∀ i ∈ S, i ∉ T → ∑ᶠ d, B i d = 1 := by
    intro i hi hT
    rw [finsum_eq_single _ (u i)]
    · simp [hind i hi hT]
    · intro d hd; simp [hind i hi hT, hd]
  rw [finprod_mem_eq_prod_of_subset _ (t := T) ?_ hTS]
  swap
  · rintro i ⟨hiS, hi⟩
    by_contra hT
    exact hi (hone i hiS hT)
  let P : ∀ i : T, Finset (D i) := fun i => (hfin i (hTS i.2)).toFinset
  have hsum : ∀ i : T, ∑ᶠ d, B i d = ∑ d ∈ P i, B i d := fun i =>
    finsum_eq_sum_of_support_subset _ (by simp [P])
  rw [← Finset.prod_coe_sort T, Finset.prod_congr rfl (fun i _ => hsum i), Finset.prod_univ_sum]
  symm
  apply finsum_eq_sum_of_support_subset
  intro f hf
  rw [Function.mem_support, Finset.prod_ne_zero_iff] at hf
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  simpa [P] using hf i (Finset.mem_univ _)
end GlobalTheory.LocalGrouping
