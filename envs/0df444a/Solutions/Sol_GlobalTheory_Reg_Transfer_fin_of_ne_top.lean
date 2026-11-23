-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.fin_of_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:33.615329+00:00
-- url     : https://prove2.me/submissions/705ae95b-e7a0-467b-9613-37e5356abd69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre

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
theorem _root_.solution {r : EReal} (h : r ≠ ⊤) (h' : r ≠ ⊥) : ∃ t : ℝ, r = (t : EReal) :=
  ⟨r.toReal, (EReal.coe_toReal h h').symm⟩
end GlobalTheory.Reg.Transfer
