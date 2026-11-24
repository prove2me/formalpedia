-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.exists_of_dlt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:51:46.979039+00:00
-- url     : https://prove2.me/submissions/db6b473d-0511-42e2-b1f3-10955e07914a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.Window
variable {K : UQ} (B : InvAlg K) {ι : Type}
namespace GlobalTheory.UnitLemma.Desc.Window
theorem _root_.solution {π : ι → B.A} {I : Finset ι} {f : B.A → ℚ} {y : B.A}
    (h : dlt π I f y ≠ 0) : ∃ J ⊆ I, f ((∏ j ∈ J, π j) * y) ≠ 0 := by
  obtain ⟨J, hJ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨J, Finset.mem_powerset.1 hJ, right_ne_zero_of_mul hne⟩
end GlobalTheory.UnitLemma.Desc.Window
