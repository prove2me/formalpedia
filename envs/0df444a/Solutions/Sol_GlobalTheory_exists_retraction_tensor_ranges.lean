-- Prove2me | solution 1 for GlobalTheory.exists_retraction_tensor_ranges
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:05:49.588799+00:00
-- url     : https://prove2.me/submissions/76e66c13-ff07-44b0-b75e-9fced730e68e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_rangeRestrict_comp_subtype_of_orthogonal
import Theorems.Thm_GlobalTheory_rangeRestrict_comp_subtype_of_orthogonal_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
variable {K : Type u} [CommRing K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V']
namespace GlobalTheory
theorem _root_.solution {f : ℕ → Module.End K V} {g : ℕ → Module.End K V'}
    (hf : ∀ p q, f p * f q = if p = q then f p else 0)
    (hg : ∀ p q, g p * g q = if p = q then g p else 0) (S : Finset (ℕ × ℕ)) :
    ∃ (I : (∀ x : S, LinearMap.range (f x.1.1) ⊗[K] LinearMap.range (g x.1.2)) →ₗ[K] V ⊗[K] V')
      (Q : V ⊗[K] V' →ₗ[K] ∀ x : S, LinearMap.range (f x.1.1) ⊗[K] LinearMap.range (g x.1.2)),
      (∀ z, I (Q z) = ∑ x ∈ S, TensorProduct.map (f x.1) (g x.2) z) ∧ ∀ w, Q (I w) = w := by
  refine ⟨∑ x : S, TensorProduct.map (LinearMap.range (f x.1.1)).subtype
      (LinearMap.range (g x.1.2)).subtype ∘ₗ LinearMap.proj x,
    LinearMap.pi fun x => TensorProduct.map (f x.1.1).rangeRestrict (g x.1.2).rangeRestrict,
    fun z => ?_, fun w => funext fun x => ?_⟩
  · rw [LinearMap.sum_apply, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.pi_apply]
    rw [TensorProduct.map_map]
    rfl
  · rw [LinearMap.sum_apply, LinearMap.pi_apply, map_sum, Finset.sum_eq_single x]
    · simp only [LinearMap.comp_apply, LinearMap.proj_apply]
      rw [TensorProduct.map_map, rangeRestrict_comp_subtype_of_orthogonal hf,
        rangeRestrict_comp_subtype_of_orthogonal hg, TensorProduct.map_id, LinearMap.id_apply]
    · intro y _ hy
      simp only [LinearMap.comp_apply, LinearMap.proj_apply]
      rw [TensorProduct.map_map]
      by_cases h : x.1.1 = y.1.1
      · have h' : x.1.2 ≠ y.1.2 := fun h' => hy (Subtype.ext (Prod.ext h h')).symm
        rw [rangeRestrict_comp_subtype_of_orthogonal_of_ne hg h', TensorProduct.map_zero_right,
          LinearMap.zero_apply]
      · rw [rangeRestrict_comp_subtype_of_orthogonal_of_ne hf h, TensorProduct.map_zero_left,
          LinearMap.zero_apply]
    · simp
end GlobalTheory
