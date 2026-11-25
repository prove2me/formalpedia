-- Prove2me | solution 1 for GroundTheory.Global.algHom_kummerExtension_mem_fieldRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:55:00.368683+00:00
-- url     : https://prove2.me/submissions/a5654cba-2438-4c99-ab84-38827c70b819

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Degree
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingKummer
import Theorems.Thm_GroundTheory_Global_kummerExtension_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Module IntermediateField GroundTheory.ProfCoh
open scoped TensorProduct
variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {Ω : Type*} [Field Ω] [Algebra K Ω] {Δ : Subgroup Kˣ}
  {F E : Type*} [Field F] [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
  [IsScalarTower K F E]
namespace GroundTheory.Global
theorem _root_.solution (ι : kummerExtension K n Ω Δ →ₐ[K] E)
    (h : ∀ a ∈ Δ, ∃ x : F, x ^ n = algebraMap K F (a : K)) (m : kummerExtension K n Ω Δ) :
    ι m ∈ (algebraMap F E).fieldRange := by
  have key : ∀ (y : kummerExtension K n Ω Δ), ∀ a ∈ Δ, (y : Ω) ^ n = algebraMap K Ω (a : K) →
      ι y ∈ (algebraMap F E).fieldRange := by
    intro y a ha hy
    obtain ⟨x, hx⟩ := h a ha
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
    have hζ' : IsPrimitiveRoot (algebraMap K E ζ) n :=
      hζ.map_of_injective (algebraMap K E).injective
    have hx0 : algebraMap F E x ≠ 0 := by
      refine (map_ne_zero _).2 fun hx0 ↦ ?_
      rw [hx0, zero_pow (NeZero.ne n)] at hx
      exact a.ne_zero ((algebraMap K F).injective (by rw [← hx, map_zero]))
    have hpow : ι y ^ n = algebraMap F E x ^ n := by
      rw [← map_pow, kummerExtension_pow_eq hy, ι.commutes, ← map_pow, hx,
        ← IsScalarTower.algebraMap_apply]
    have hroot : (ι y / algebraMap F E x) ^ n = 1 := by
      rw [div_pow, hpow, div_self (pow_ne_zero _ hx0)]
    obtain ⟨k, -, hk⟩ := hζ'.eq_pow_of_pow_eq_one hroot
    refine ⟨algebraMap K F ζ ^ k * x, ?_⟩
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply, hk, div_mul_cancel₀ _ hx0]
  obtain ⟨m, hm⟩ := m
  induction hm using IntermediateField.adjoin_induction with
  | mem α hα =>
    obtain ⟨a, ha, hαa⟩ := id hα
    exact key _ a ha hαa
  | algebraMap x =>
    refine ⟨algebraMap K F x, ?_⟩
    rw [← IsScalarTower.algebraMap_apply]
    exact (ι.commutes x).symm
  | add x y hx hy ihx ihy =>
    show ι (⟨x, hx⟩ + ⟨y, hy⟩) ∈ _
    rw [map_add]
    exact add_mem ihx ihy
  | inv x hx ih =>
    show ι (⟨x, hx⟩⁻¹) ∈ _
    rw [map_inv₀]
    exact inv_mem ih
  | mul x y hx hy ihx ihy =>
    show ι (⟨x, hx⟩ * ⟨y, hy⟩) ∈ _
    rw [map_mul]
    exact mul_mem ihx ihy
end GroundTheory.Global
