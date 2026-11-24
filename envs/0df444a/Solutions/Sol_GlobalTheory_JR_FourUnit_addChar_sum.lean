-- Prove2me | solution 1 for GlobalTheory.JR.FourUnit.addChar_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:58:39.535884+00:00
-- url     : https://prove2.me/submissions/b359258e-62f7-4b9d-a4b8-c2f2f4d377e8

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockUnitIndicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.FourUnit
namespace GlobalTheory.JR.FourUnit
theorem _root_.solution {A : Type} [AddCommMonoid A] (ψ : AddChar A ℂ) {ι : Type} (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
end GlobalTheory.JR.FourUnit
