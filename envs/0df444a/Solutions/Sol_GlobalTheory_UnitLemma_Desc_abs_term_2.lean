-- Prove2me | solution 2 for GlobalTheory.UnitLemma.Desc.abs_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:36:47.899881+00:00
-- url     : https://prove2.me/submissions/69e02f87-3153-4905-bfc3-0069eab948cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_abs_indM
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_abs_indD
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_abs_dlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology Classical
variable {K : UQ} (B : InvAlg K) {ι : Type}
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A) :
    |term B π I I' u s M| ≤ 2 ^ I.card * 2 ^ I'.card := by
  unfold term
  rw [abs_mul]
  exact mul_le_mul (abs_dlt _ _ _ (abs_indM B M) _) (abs_dlt _ _ _ (abs_indD B M) _) (abs_nonneg _) (by positivity)
end GlobalTheory.UnitLemma.Desc
