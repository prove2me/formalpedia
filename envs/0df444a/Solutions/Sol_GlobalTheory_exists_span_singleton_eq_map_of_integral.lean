-- Prove2me | solution 1 for GlobalTheory.exists_span_singleton_eq_map_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:00.351203+00:00
-- url     : https://prove2.me/submissions/43dc3999-92f1-42fb-95bc-7af41b2ec244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] (𝔟 : Ideal (𝓞 K)) (β : M) (h𝔟 : 𝔟 ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ 𝔟, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    ∃ β₀ : 𝓞 M, (β₀ : M) = β ∧ Ideal.span {β₀} = 𝔟.map (algebraMap (𝓞 K) (𝓞 M)) := by
  have hint : IsIntegral ℤ β := by
    have := h₁ 1 (fun b _ => by simpa using RingOfIntegers.isIntegral_coe b)
    simpa using this
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : 𝓞 M, (β₀ : M) = β := ⟨⟨β, hint⟩, rfl⟩
  refine ⟨β₀, hβ₀, le_antisymm ?_ ?_⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have hone : (1 : K) ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
        (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹) := by
      rw [FractionalIdeal.coe_ideal_mul_inv 𝔟 h𝔟]
      exact FractionalIdeal.one_mem_one _
    have key : ∀ r ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
        (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹),
        ∃ z ∈ 𝔟.map (algebraMap (𝓞 K) (𝓞 M)), (z : M) = β * algebraMap K M r := by
      intro r hr
      refine FractionalIdeal.mul_induction_on
        (C := fun r => ∃ z ∈ 𝔟.map (algebraMap (𝓞 K) (𝓞 M)), (z : M) = β * algebraMap K M r)
        hr ?_ ?_
      · intro i hi j hj
        obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
        have h0 : (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
          FractionalIdeal.coeIdeal_ne_zero.2 h𝔟
        have hj' := (FractionalIdeal.mem_inv_iff h0).1 hj
        have hI : IsIntegral ℤ (β * algebraMap K M j) := by
          refine h₁ j fun c hc => ?_
          obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1
            (hj' _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨c, hc, rfl⟩))
          have : j * (c : K) = (w : K) := hw.symm
          rw [this]
          exact RingOfIntegers.isIntegral_coe w
        refine ⟨algebraMap (𝓞 K) (𝓞 M) b * ⟨_, hI⟩,
          Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb), ?_⟩
        change algebraMap K M (b : K) * (β * algebraMap K M j) =
          β * algebraMap K M ((b : K) * j)
        rw [map_mul]; ring
      · rintro x y ⟨z, hz, hx⟩ ⟨w, hw, hy⟩
        refine ⟨z + w, Ideal.add_mem _ hz hw, ?_⟩
        change (z : M) + (w : M) = _
        rw [hx, hy, map_add]; ring
    obtain ⟨z, hz, hz'⟩ := key 1 hone
    have : β₀ = z := by
      apply RingOfIntegers.ext
      rw [hz', hβ₀]; simp
    rw [this]; exact hz
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨⟨_, h₂ y hy⟩, ?_⟩
    apply RingOfIntegers.ext
    change β⁻¹ * algebraMap K M (y : K) * (β₀ : M) = algebraMap K M (y : K)
    rw [hβ₀]
    field_simp
end GlobalTheory
