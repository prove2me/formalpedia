-- Prove2me | solution 2 for GlobalTheory.DoubleCosetEuler.finsum_pi_prod_eq_prod_finsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:25:07.654548+00:00
-- url     : https://prove2.me/submissions/cbbbd667-052e-4e6d-9090-fea4ffcab840

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumDoubleCosetEqFinprodLocalSums

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
open GlobalTheory GlobalTheory.DoubleCosetEuler
namespace GlobalTheory.DoubleCosetEuler
theorem _root_.solution (J : Type) [Fintype J] (α : J → Type) (f : ∀ j, α j → ℂ)
    (hf : ∀ j, (Function.support (f j)).Finite) :
    ∑ᶠ y : (∀ j, α j), ∏ j, f j (y j) = ∏ j, ∑ᶠ a, f j a := by
  have hR : ∀ j, ∑ᶠ a, f j a = ∑ a ∈ (hf j).toFinset, f j a := fun j =>
    finsum_eq_sum_of_support_subset _ (by simp)
  simp_rw [hR]
  rw [Finset.prod_univ_sum]
  apply finsum_eq_sum_of_support_subset
  intro y hy
  rw [Function.mem_support, Finset.prod_ne_zero_iff] at hy
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro j
  simpa using hy j (Finset.mem_univ j)
end GlobalTheory.DoubleCosetEuler
