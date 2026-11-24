-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Move.term_mulLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:10:32.858081+00:00
-- url     : https://prove2.me/submissions/74844089-1401-4161-8b5d-d75e4aded070

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixedBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SignedInvolutionStableLatticeSumMulFixedUnit
import Theorems.Thm_GlobalTheory_UnitLemma_Move_mem_mulLat
import Theorems.Thm_GlobalTheory_UnitLemma_Move_inDual_mulLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Move
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.Move
theorem _root_.solution {ι : Type} (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A)
    (y : B.Aˣ) :
    term B π I I' ((y : B.A) * u) s (mulLat K.O (y : B.A) M) = term B π I I' u ((y : B.A) * s) M := by
  classical
  unfold term dlt
  congr 1
  · refine Finset.sum_congr rfl fun J _ => ?_
    unfold indM
    have e : ((y⁻¹ : B.Aˣ) : B.A) * ((∏ j ∈ J, π j) * ((y : B.A) * u)) = (∏ j ∈ J, π j) * u := by
      rw [mul_left_comm, Units.inv_mul_cancel_left]
    simp only [mem_mulLat, e]
  · refine Finset.sum_congr rfl fun J _ => ?_
    unfold indD
    have e : (y : B.A) * ((∏ j ∈ J, π j) * s) = (∏ j ∈ J, π j) * ((y : B.A) * s) := by ring
    simp only [inDual_mulLat, e]
end GlobalTheory.UnitLemma.Move
