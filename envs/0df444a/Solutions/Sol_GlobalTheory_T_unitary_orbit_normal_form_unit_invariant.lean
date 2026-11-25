-- Prove2me | solution 1 for GlobalTheory.T.unitary_orbit_normal_form_unit_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:25:29.165356+00:00
-- url     : https://prove2.me/submissions/d3df78c5-6c18-42f7-8b68-6679966c6dcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitNormalFormUnitInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitNormalFormUnitInvariantStatement
import Theorems.Thm_GlobalTheory_JR_Step_uNormal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (X : Hn (r + 1) F E) (a : Inv (r + 1) F), HasInv X a → ‖a.2.1 0‖ = 1 → ∃ (g : Matrix.unitaryGroup (Fin (r + 1)) E) (X' : Hn r F E) (ν : E), ν * star ν = algebraMap F E (a.2.1 0) ∧ actU g X = GlobalTheory.JR.Step.liftH X' ν a.2.2 := by
  first | exact @GlobalTheory.JR.Step.uNormal | exact GlobalTheory.JR.Step.uNormal | (intros; apply GlobalTheory.JR.Step.uNormal <;> assumption)
end _root_.GlobalTheory.T
