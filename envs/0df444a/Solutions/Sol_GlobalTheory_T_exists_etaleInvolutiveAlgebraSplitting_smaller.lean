-- Prove2me | solution 1 for GlobalTheory.T.exists_etaleInvolutiveAlgebraSplitting_smaller
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:06:55.444341+00:00
-- url     : https://prove2.me/submissions/ee84d1ec-5cf5-4874-8d4b-f72ecc4a3a14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleInvolutiveAlgebraSplittingSmaller
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleInvolutiveAlgebraSplittingSmallerStatement
import Theorems.Thm_GlobalTheory_JR_EtQuot_exists_splitting


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Nontrivial A.K → ¬ IsField A.K → ∃ (A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L), IsSplitting A A₁ A₂ eK eL ∧ Module.finrank F A₁.K < Module.finrank F A.K ∧ Module.finrank F A₂.K < Module.finrank F A.K := by
  first | exact @GlobalTheory.JR.EtQuot.exists_splitting | exact GlobalTheory.JR.EtQuot.exists_splitting | (intros; apply GlobalTheory.JR.EtQuot.exists_splitting <;> assumption)
end _root_.GlobalTheory.T
