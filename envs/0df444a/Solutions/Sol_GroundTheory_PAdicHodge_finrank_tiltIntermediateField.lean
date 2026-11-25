-- Prove2me | solution 1 for GroundTheory.PAdicHodge.finrank_tiltIntermediateField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:53.612858+00:00
-- url     : https://prove2.me/submissions/ce9763eb-7b79-47d1-adde-3763eb07703f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApprox
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
import Definitions.Def_GroundTheory_PAdicHodge_CompletedAlgClosure
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCharP
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgClosed
import Definitions.Def_GroundTheory_PAdicHodge_TiltEquiv
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_untiltField
import Theorems.Thm_GroundTheory_PAdicHodge_tiltIntermediateField_untiltField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C] [IsAlgClosed C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
variable [IsPerfectoidField C p]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (L : IntermediateField K C) [FiniteDimensional K L] :
    Module.finrank K♭ (tiltIntermediateField p L) = Module.finrank K L := by
  obtain ⟨M, hM, rfl⟩ := exists_eq_untiltField (p := p) L
  have h : tiltIntermediateField p (untiltField K C p M) = M :=
    tiltIntermediateField_untiltField M
  rw [h, finrank_untiltField]
end GroundTheory.PAdicHodge
