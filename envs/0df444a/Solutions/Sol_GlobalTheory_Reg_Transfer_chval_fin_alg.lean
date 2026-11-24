-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.chval_fin_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:54:08.826185+00:00
-- url     : https://prove2.me/submissions/19c96405-7e80-486a-a965-aaec8063ef6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Theorems.Thm_GlobalTheory_Reg_Transfer_vr_one
import Theorems.Thm_GlobalTheory_Reg_Transfer_chval_fin_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {A : Type} [CommRing A] [IsDomain A]
namespace GlobalTheory.Reg.Transfer
theorem _root_.solution (φ : A →+* V) (e : ℕ) (a : A) (ha : φ a ≠ 0) :
    ChV φ e (algebraMap A (FractionRing A) a) ((vr e (φ a) : ℝ) : EReal) := by
  refine (chval_fin_iff φ e _ _).2 ⟨a, 1, ?_, ha, ?_, ?_⟩
  · rw [map_one]; exact one_ne_zero
  · rw [map_one, mul_one]
  · rw [map_one, vr_one, sub_zero]
end GlobalTheory.Reg.Transfer
