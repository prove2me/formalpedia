-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.chval_fin_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:39.269797+00:00
-- url     : https://prove2.me/submissions/77156a29-4706-420b-9d85-56193737eaeb

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
theorem _root_.solution (φ : A →+* V) (e : ℕ) : ChV φ e (1 : FractionRing A) ((0 : ℝ) : EReal) := by
  refine (chval_fin_iff φ e _ _).2 ⟨1, 1, ?_, ?_, ?_, ?_⟩ <;> simp [vr_one]
end GlobalTheory.Reg.Transfer
