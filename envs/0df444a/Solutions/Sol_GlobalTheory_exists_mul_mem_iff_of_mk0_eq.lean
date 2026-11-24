-- Prove2me | solution 1 for GlobalTheory.exists_mul_mem_iff_of_mk0_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:44:41.774895+00:00
-- url     : https://prove2.me/submissions/1055e28d-ea1b-4800-8754-908f57edd375

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MeanLogCovolumeEqMeanClassGroup
import Theorems.Thm_GlobalTheory_HasQExpansion_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField
open scoped nonZeroDivisors Real UpperHalfPlane
noncomputable section
open GlobalTheory
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution (𝔞 𝔟 𝔡 : (Ideal (𝓞 K))⁰)
    (h : ClassGroup.mk0 𝔡 * ClassGroup.mk0 𝔟 = ClassGroup.mk0 𝔞) :
    ∃ u : K, u ≠ 0 ∧ ∀ t : K, (∀ b ∈ (𝔟 : Ideal (𝓞 K)), ∃ a ∈ (𝔞 : Ideal (𝓞 K)),
      u * t * (b : K) = a) ↔ ∃ d ∈ (𝔡 : Ideal (𝓞 K)), t = d := by
  rw [← map_mul, ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, e⟩ := h
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx
  have hy' : (y : K) ≠ 0 := by exact_mod_cast hy
  have hB : ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (nonZeroDivisors.coe_ne_zero 𝔟)
  have e' := congrArg (fun I : Ideal (𝓞 K) => (I : FractionalIdeal (𝓞 K)⁰ K)) e
  simp only [Submonoid.coe_mul, FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.coeIdeal_span_singleton] at e'
  have hY : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K y) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 hy'
  have key : ((𝔞 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) / (𝔟 : Ideal (𝓞 K)) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : K) / (y : K)) * (𝔡 : Ideal (𝓞 K)) := by
    rw [div_eq_iff hB]
    apply mul_left_cancel₀ hY
    rw [← e', ← mul_assoc, ← mul_assoc, ← mul_assoc,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 3
    change (x : K) = (y : K) * _
    field_simp
  refine ⟨x / y, div_ne_zero hx' hy', fun t => ?_⟩
  have h1 : (∀ b ∈ (𝔟 : Ideal (𝓞 K)), ∃ a ∈ (𝔞 : Ideal (𝓞 K)), (x : K) / y * t * (b : K) = a) ↔
      (x : K) / y * t ∈ ((𝔞 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) / (𝔟 : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.mem_div_iff_of_ne_zero hB]
    constructor
    · intro h b hb
      obtain ⟨b, hb', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hb
      obtain ⟨a, ha, e⟩ := h b hb'
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨a, ha, e.symm⟩
    · intro h b hb
      obtain ⟨a, ha, e⟩ := (FractionalIdeal.mem_coeIdeal _).1
        (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hb))
      exact ⟨a, ha, e.symm⟩
  rw [h1, key, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨d, hd, e⟩
    obtain ⟨d, hd', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hd
    exact ⟨d, hd', mul_left_cancel₀ (div_ne_zero hx' hy') e⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨_, FractionalIdeal.mem_coeIdeal_of_mem _ hd, rfl⟩
end GlobalTheory
