-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.vr_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:54:12.836788+00:00
-- url     : https://prove2.me/submissions/9192c459-24bb-43ac-b980-5895c4747c6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Theorems.Thm_GlobalTheory_Reg_Transfer_ne_zero_map
import Theorems.Thm_Formalism_L2_Pj_vV_mul


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
theorem _root_.solution (e : ℕ) {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : vr e (x * y) = vr e x + vr e y := by
  unfold vr
  rw [map_mul, vV_mul (ne_zero_map hx) (ne_zero_map hy)]
  push_cast
  ring
end GlobalTheory.Reg.Transfer
