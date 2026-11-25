-- Prove2me | solution 1 for HcInf.cayS_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:58.132246+00:00
-- url     : https://prove2.me/submissions/b0dbdf80-6e54-4d83-8031-01f48233287f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayK

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
theorem _root_.solution (hI : CayInvIff) (P Q : ℕ) (V : Set (lieU P Q)) :
    cayS V = cayS Set.univ ∩ cayInv P Q ⁻¹' V := by
  ext g
  simp only [cayS, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ, true_and]
  constructor
  · rintro ⟨X, hX, hg⟩
    exact ⟨⟨X, hg⟩, by rw [hI P Q g X hg]; exact hX⟩
  · rintro ⟨⟨X, hg⟩, hV⟩
    exact ⟨X, by rw [← hI P Q g X hg]; exact hV, hg⟩
end HcInf
