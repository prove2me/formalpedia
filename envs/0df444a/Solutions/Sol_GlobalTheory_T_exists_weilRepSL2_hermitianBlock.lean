-- Prove2me | solution 1 for GlobalTheory.T.exists_weilRepSL2_hermitianBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:24:22.475984+00:00
-- url     : https://prove2.me/submissions/2502d22d-7a9f-446c-903b-914bfc747a67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepSL2HermitianBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepSL2HermitianBlockStatement
import Theorems.Thm_GlobalTheory_weilSL2_hermitian


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
theorem _root_.solution : WeilEt → GammaOne → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Hn r F E → ℂ) → Hn r F E → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t X, W (nS t) f X = ψ (t * Algebra.trace F E (star X.2.1 ⬝ᵥ X.2.1) / 2) * f X) ∧ W (wS F) f = fourU M ψ f := by
  first | exact @GlobalTheory.weilSL2_hermitian | exact GlobalTheory.weilSL2_hermitian | (intros; apply GlobalTheory.weilSL2_hermitian <;> assumption)
end _root_.GlobalTheory.T
