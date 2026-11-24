-- Prove2me | solution 1 for GlobalTheory.UnitLemma.TorusPts.f_mul_tt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:40:40.75413+00:00
-- url     : https://prove2.me/submissions/01c41897-456a-49f1-8cb6-85503723bd36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposi

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
theorem _root_.solution (f h c d : I → A) (hf : ∀ i, f i * f i = f i) (hff : ∀ i j, i ≠ j → f i * f j = 0)
    (hfh : ∀ i j, f i * h j = 0) (j : I) : f j * tt f h c d = c j * f j := by
  classical
  unfold tt
  rw [mul_add, Finset.mul_sum, Finset.sum_eq_single j]
  · linear_combination (c j - 1) * hf j + (d j - 1) * hfh j j
  · intro i _ hi
    linear_combination (c i - 1) * hff j i hi.symm + (d i - 1) * hfh j i
  · simp
end GlobalTheory.UnitLemma.TorusPts
