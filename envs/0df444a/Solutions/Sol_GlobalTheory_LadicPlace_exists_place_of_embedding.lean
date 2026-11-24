-- Prove2me | solution 1 for GlobalTheory.LadicPlace.exists_place_of_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:50:26.56132+00:00
-- url     : https://prove2.me/submissions/bcf5b352-028b-433d-8aec-46b9052a7ca2

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormEmbeddingIntegerLeOne
import Theorems.Thm_GlobalTheory_LadicPlace_norm_embedding_integer_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory GlobalTheory.LadicPlace
namespace GlobalTheory.LadicPlace
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (τ : E →+* Qbar l),
      ∃ v : HeightOneSpectrum (𝓞 E), ∀ x : E, v.valuation E x < 1 ↔ ‖τ x‖ < 1 := by
  intro E _ _ l hl τ
  have hle : ∀ a : 𝓞 E, ‖τ (a : E)‖ ≤ 1 := norm_embedding_integer_le_one τ
  let P : Ideal (𝓞 E) :=
    { carrier := {a | ‖τ (a : E)‖ < 1}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [RingOfIntegers.coe_eq_algebraMap, map_add, map_add]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [RingOfIntegers.coe_eq_algebraMap, smul_eq_mul, map_mul, map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) ha }
  have hP : ∀ a : 𝓞 E, a ∈ P ↔ ‖τ (algebraMap (𝓞 E) E a)‖ < 1 := fun a => Iff.rfl
  have hone : ∀ a : 𝓞 E, a ∉ P → ‖τ (algebraMap (𝓞 E) E a)‖ = 1 := fun a ha =>
    le_antisymm (hle a) (not_lt.mp (fun h => ha ((hP a).mpr h)))
  have hprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hP]; simp
    · intro a b hab
      by_contra hn
      rw [not_or] at hn
      rw [hP, map_mul, map_mul, norm_mul, hone a hn.1, hone b hn.2] at hab
      simp at hab
  have hlP : (l : 𝓞 E) ∈ P := by
    rw [hP, map_natCast, map_natCast]
    have h1 : ((l : ℕ) : PadicAlgCl l) = ((l : ℚ_[l]) : PadicAlgCl l) := by
      simp
    rw [h1, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hlP
    exact hl.out.ne_zero (by exact_mod_cast hlP)
  let v : HeightOneSpectrum (𝓞 E) := ⟨P, hprime, hne⟩
  have key : ∀ x : E, v.valuation E x ≤ 1 → ∃ a s : 𝓞 E, s ∉ P ∧
      x * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a := by
    intro x hx
    obtain ⟨a, s, h⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
    exact ⟨a, s, s.2, h⟩
  refine ⟨v, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨a, s, hs, h⟩ := key x hx.le
    have ha : a ∈ P := by
      have : v.valuation E (algebraMap (𝓞 E) E a) < 1 := by
        rw [← h, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (v.valuation_le_one s)) hx
      exact (v.valuation_lt_one_iff_mem a).mp this
    rw [hP, ← h, map_mul, norm_mul, hone s hs, mul_one] at ha
    exact ha
  · by_contra hn
    have hn' : 1 ≤ v.valuation E x := not_lt.mp hn
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hn'
    have hinv : v.valuation E x⁻¹ ≤ 1 := by
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ hn'
    obtain ⟨a, s, hs, h⟩ := key _ hinv
    have h2 : algebraMap (𝓞 E) E s = x * algebraMap (𝓞 E) E a := by
      rw [← h, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
    have h3 := hone s hs
    rw [h2, map_mul, norm_mul] at h3
    have h4 := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx (hle a)
    exact absurd h3 h4.ne
end GlobalTheory.LadicPlace
