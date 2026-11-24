-- Prove2me | solution 1 for GlobalTheory.T.exists_power_basis_of_charpoly_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:21:14.112479+00:00
-- url     : https://prove2.me/submissions/94f40934-ea65-4542-b2c8-ba1e1b72a7fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparableStatement
import Theorems.Thm_GlobalTheory_UnitLemma_exists_basis_pow_of_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A, ∀ i, e i = B.g ^ (i : ℕ) := by
  first | exact @GlobalTheory.UnitLemma.exists_basis_pow_of_separable | exact GlobalTheory.UnitLemma.exists_basis_pow_of_separable | (intros; apply GlobalTheory.UnitLemma.exists_basis_pow_of_separable <;> assumption)
end _root_.GlobalTheory.T
