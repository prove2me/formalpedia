-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.nval_eq_vr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:52.241591+00:00
-- url     : https://prove2.me/submissions/3eafb5d0-7516-480e-933a-a2893c141d9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Theorems.Thm_GlobalTheory_Reg_Transfer_ne_zero_map
import Theorems.Thm_Formalism_L2_Pj_nval_of_ne


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
theorem _root_.solution (e : ℕ) {x : V} (hx : x ≠ 0) :
    nval V e (algebraMap V (FractionRing V) x) = (vr e x : EReal) := by
  rw [nval_of_ne (ne_zero_map hx)]
  rfl
end GlobalTheory.Reg.Transfer
