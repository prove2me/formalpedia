-- Prove2me | solution 1 for GlobalTheory.UnitLemma.BaseChange.herm_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:51:52.149421+00:00
-- url     : https://prove2.me/submissions/450599cf-ec59-4d8f-a1f5-bc2ffefc4224

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
theorem _root_.solution {ι : Type} (s : Finset ι) (x y : B.A) (f : ι → B.A) :
    B.herm x y (∑ k ∈ s, f k) = ∑ k ∈ s, B.herm x y (f k) := by
  unfold InvAlg.herm
  rw [map_sum, Finset.mul_sum, map_sum]
end GlobalTheory.UnitLemma.BaseChange
