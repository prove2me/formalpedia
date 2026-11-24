-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ProdCount.finsum_prod_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:58:59.3748+00:00
-- url     : https://prove2.me/submissions/9d68fc48-af9a-4f24-8ade-1e2633979b06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ProdCount
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
namespace GlobalTheory.UnitLemma.ProdCount
theorem _root_.solution {α β : Type} (f : α → ℚ) (g : β → ℚ) :
    ∑ᶠ p : α × β, f p.1 * g p.2 = (∑ᶠ a, f a) * ∑ᶠ b, g b := by
  classical
  by_cases hf0 : f = 0
  · simp [hf0]
  by_cases hg0 : g = 0
  · simp [hg0]
  obtain ⟨a0, ha0⟩ := Function.ne_iff.1 hf0
  obtain ⟨b0, hb0⟩ := Function.ne_iff.1 hg0
  have hs : Function.support (fun p : α × β => f p.1 * g p.2) = Function.support f ×ˢ Function.support g := by
    ext p
    simp [Function.mem_support]
  by_cases hf : (Function.support f).Finite
  · by_cases hg : (Function.support g).Finite
    · rw [finsum_eq_sum_of_support_subset (s := hf.toFinset) f (by simp),
        finsum_eq_sum_of_support_subset (s := hg.toFinset) g (by simp),
        finsum_eq_sum_of_support_subset (s := hf.toFinset ×ˢ hg.toFinset) _ (by rw [hs]; simp),
        Finset.sum_mul_sum, Finset.sum_product]
    · rw [finsum_of_infinite_support hg, mul_zero, finsum_of_infinite_support]
      rw [hs]
      exact Set.Infinite.prod_right hg ⟨a0, ha0⟩
  · rw [finsum_of_infinite_support hf, zero_mul, finsum_of_infinite_support]
    rw [hs]
    exact Set.Infinite.prod_left hf ⟨b0, hb0⟩
end GlobalTheory.UnitLemma.ProdCount
