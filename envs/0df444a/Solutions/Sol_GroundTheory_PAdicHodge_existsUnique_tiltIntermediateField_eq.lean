-- Prove2me | solution 1 for GroundTheory.PAdicHodge.existsUnique_tiltIntermediateField_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:19.043859+00:00
-- url     : https://prove2.me/submissions/5f6c4fa5-fcc4-4df0-8941-ecb59843c7af

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
theorem _root_.solution (M : IntermediateField K♭ C♭)
    [FiniteDimensional K♭ M] :
    ∃! L : IntermediateField K C, ∃ _ : FiniteDimensional K L, tiltIntermediateField p L = M := by
  refine ⟨untiltField K C p M, ⟨inferInstance, tiltIntermediateField_untiltField M⟩, ?_⟩
  rintro L ⟨hL, hLM⟩
  obtain ⟨M', hM', rfl⟩ := exists_eq_untiltField (p := p) L
  have h : tiltIntermediateField p (untiltField K C p M') = M' :=
    tiltIntermediateField_untiltField M'
  rw [h] at hLM
  rw [hLM]
end GroundTheory.PAdicHodge
