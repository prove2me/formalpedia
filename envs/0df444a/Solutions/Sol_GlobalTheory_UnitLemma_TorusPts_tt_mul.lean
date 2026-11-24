-- Prove2me | solution 1 for GlobalTheory.UnitLemma.TorusPts.tt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:00:15.803133+00:00
-- url     : https://prove2.me/submissions/da2d534a-d0db-48a0-b67b-f750adf8b6b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposi
import Theorems.Thm_GlobalTheory_UnitLemma_TorusPts_f_mul_tt
import Theorems.Thm_GlobalTheory_UnitLemma_TorusPts_tt_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TorusPts
variable {A : Type} [CommRing A] {I : Type} [Fintype I]
namespace GlobalTheory.UnitLemma.TorusPts
theorem _root_.solution (f h c d c' d' : I → A) (hf : ∀ i, f i * f i = f i) (hff : ∀ i j, i ≠ j → f i * f j = 0)
    (hh : ∀ i, h i * h i = h i) (hhh : ∀ i j, i ≠ j → h i * h j = 0)
    (hfh : ∀ i j, f i * h j = 0) : tt f h c d * tt f h c' d' = tt f h (c * c') (d * d') := by
  have h1 := f_mul_tt f h c' d' hf hff hfh
  have h2 := f_mul_tt h f d' c' hh hhh (fun i j => by rw [mul_comm]; exact hfh j i)
  rw [← tt_swap] at h2
  have h3 : tt f h c d * tt f h c' d' =
      tt f h c' d' + ∑ i, ((c i - 1) * (f i * tt f h c' d') + (d i - 1) * (h i * tt f h c' d')) := by
    conv_lhs => arg 1; unfold tt
    rw [add_mul, one_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h3]
  simp only [h1, h2]
  unfold tt
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.mul_apply]; ring
end GlobalTheory.UnitLemma.TorusPts
