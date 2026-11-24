-- Prove2me | solution 1 for GlobalTheory.UnitLemma.BaseChange.herm_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:51:50.690959+00:00
-- url     : https://prove2.me/submissions/7a407e24-be06-4e02-a669-580b1151f654

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ValIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OrthonormalIffUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.BaseChange
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.BaseChange
theorem _root_.solution {ι : Type} (s : Finset ι) (x : B.A) (f : ι → B.A) (z : B.A) :
    B.herm x (∑ k ∈ s, f k) z = ∑ k ∈ s, B.herm x (f k) z := by
  unfold InvAlg.herm
  rw [Finset.mul_sum, Finset.sum_mul, map_sum]
end GlobalTheory.UnitLemma.BaseChange
