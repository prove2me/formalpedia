-- Prove2me | solution 1 for HcInf.cayleyLoc_of_dens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:49:12.090576+00:00
-- url     : https://prove2.me/submissions/61e15386-e314-4c9c-b04f-674f68f38267

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayK
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExOm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayleyInverseMeasurable
import Theorems.Thm_HcInf_cayley_inverse_iff
import Theorems.Thm_HcInf_cayley_inverse_measurable
import Theorems.Thm_HcInf_cayley_set_measurable
import Theorems.Thm_HcInf_cayleyLoc_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace HcInf
theorem _root_.solution (h : CayleyDens) : CayleyLoc :=
  cayleyLoc_of cayley_inverse_measurable cayley_inverse_iff cayley_set_measurable h
end HcInf
