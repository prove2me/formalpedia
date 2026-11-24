-- Prove2me | solution 1 for GlobalTheory.T.idempotentCoordinates_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:21:09.645806+00:00
-- url     : https://prove2.me/submissions/2443dbe4-0778-48d1-baf6-35dbfd135387

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentCoordinatesStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentCoordinatesStructureStatement
import Theorems.Thm_GlobalTheory_JR_Hyp_coord_structure


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), e * e = e → star e = 1 - e → (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) ∧ (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) ∧ (∀ p, A.NL (Hyp.cc A e p) = p.1 * p.2) ∧ (∀ (ψ : AddChar F ℂ) (x : A.K) (p q : A.K × A.K), A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) ∧ (∀ (s : A.K) p, s • Hyp.cc A e p = Hyp.cc A e (s * p.1, s * p.2)) ∧ ∀ s : A.Kˣ, IsUnit (Hyp.cc A e ((s : A.K), 1)) := by
  first | exact @GlobalTheory.JR.Hyp.coord_structure | exact GlobalTheory.JR.Hyp.coord_structure | (intros; apply GlobalTheory.JR.Hyp.coord_structure <;> assumption)
end _root_.GlobalTheory.T
