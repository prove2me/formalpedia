-- Prove2me | solution 1 for GroundTheory.Global.finrank_eq_one_iff_of_kummerExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:21.391316+00:00
-- url     : https://prove2.me/submissions/0f009161-f38e-4ba1-8e5c-fb466921d733

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Degree
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingKummer
import Theorems.Thm_GroundTheory_Global_kummerExtension_pow_eq
import Theorems.Thm_GroundTheory_Global_algHom_kummerExtension_mem_fieldRange
import Theorems.Thm_GroundTheory_Global_finrank_eq_one_of_tensor_surjective

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
theorem _root_.solution [IsSepClosed Ω]
    (g : F ⊗[K] kummerExtension K n Ω Δ →ₐ[F] E) (hg : Function.Surjective g) :
    finrank F E = 1 ↔ ∀ a ∈ Δ, ∃ x : F, x ^ n = algebraMap K F (a : K) := by
  let ι : kummerExtension K n Ω Δ →ₐ[K] E :=
    (g.restrictScalars K).comp Algebra.TensorProduct.includeRight
  constructor
  · intro h1 a ha
    have hsurj : Function.Surjective (algebraMap F E) :=
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1).2
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
    have hnK : NeZero ((n : ℕ) : K) := hζ.neZero'
    have hnΩ : NeZero ((n : ℕ) : Ω) :=
      ⟨by rw [← map_natCast (algebraMap K Ω)]; exact (map_ne_zero _).2 hnK.out⟩
    obtain ⟨α, hα⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap K Ω (a : K)) n
    let y : kummerExtension K n Ω Δ := ⟨α, subset_adjoin _ _ ⟨a, ha, hα⟩⟩
    obtain ⟨x, hx⟩ := hsurj (ι y)
    refine ⟨x, (algebraMap F E).injective ?_⟩
    rw [map_pow, hx, ← map_pow, kummerExtension_pow_eq (y := y) hα, ι.commutes,
      ← IsScalarTower.algebraMap_apply]
  · intro h
    exact finrank_eq_one_of_tensor_surjective g hg fun m ↦
      algHom_kummerExtension_mem_fieldRange ι h m
end GroundTheory.Global
