-- Prove2me | solution 1 for GlobalTheory.FlatFibreRegular.exists_minimal_generators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:59:14.548287+00:00
-- url     : https://prove2.me/submissions/bdf94e8d-a561-499c-9466-bb65ea069543

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
open GlobalTheory GlobalTheory.FlatFibreRegular
namespace GlobalTheory.FlatFibreRegular
theorem _root_.solution {A : Type} [CommRing A] (𝔭 : Ideal A) [𝔭.IsPrime] (I : Ideal A)
    (hI : I.FG) :
    ∃ S : Finset A, (↑S ⊆ (I : Set A)) ∧ (∀ x ∈ I, ∃ s ∉ 𝔭, s * x ∈ Ideal.span (S : Set A)) ∧
      ∀ c : S → A, ∑ i, c i * (i : A) = 0 → ∀ i, c i ∈ 𝔭 := by
  classical
  let P : Finset A → Prop := fun S =>
    (↑S ⊆ (I : Set A)) ∧ ∀ x ∈ I, ∃ s ∉ 𝔭, s * x ∈ Ideal.span (S : Set A)
  have hex : ∃ n, ∃ S : Finset A, S.card = n ∧ P S := by
    obtain ⟨S, hS⟩ := hI
    refine ⟨S.card, S, rfl, fun a ha => ?_, fun x hx => ⟨1, ?_, ?_⟩⟩
    · rw [← hS]; exact Ideal.subset_span ha
    · exact fun h => (Ideal.IsPrime.ne_top' (I := 𝔭)) ((Ideal.eq_top_iff_one _).2 h)
    · rw [one_mul, hS]; exact hx
  obtain ⟨S, hcard, hSI, hSgen⟩ := Nat.find_spec hex
  refine ⟨S, hSI, hSgen, fun c hc k => ?_⟩
  by_contra hk
  have hlt : (S.erase k).card < Nat.find hex := by
    rw [← hcard]; exact Finset.card_erase_lt_of_mem k.2
  apply Nat.find_min hex hlt
  refine ⟨S.erase k, rfl, fun x hx => hSI (Finset.mem_of_mem_erase hx), fun x hx => ?_⟩
  obtain ⟨s, hs, hsx⟩ := hSgen x hx
  refine ⟨c k * s, fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hk hs), ?_⟩
  have key : Ideal.span (S : Set A) ≤
      Submodule.comap (LinearMap.mulLeft A (c k)) (Ideal.span ((S.erase k : Finset A) : Set A)) := by
    rw [Ideal.span_le]
    intro a ha
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    by_cases hak : a = k
    · rw [hak]
      have h1 := Finset.add_sum_erase Finset.univ (fun i : S => c i * (i : A)) (Finset.mem_univ k)
      rw [hc] at h1
      rw [eq_neg_of_add_eq_zero_left h1]
      refine neg_mem (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      exact Finset.mem_erase.2 ⟨fun h => hik (Subtype.ext h), i.2⟩
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_erase.2 ⟨hak, ha⟩))
  have := key hsx
  simpa [mul_assoc] using this
end GlobalTheory.FlatFibreRegular
