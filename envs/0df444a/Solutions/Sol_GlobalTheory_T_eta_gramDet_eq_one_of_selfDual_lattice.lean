-- Prove2me | solution 1 for GlobalTheory.T.eta_gramDet_eq_one_of_selfDual_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:22.566715+00:00
-- url     : https://prove2.me/submissions/7e239497-be54-458c-b83d-6911bb0cdfd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetEqOneOfSelfDualLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetEqOneOfSelfDualLatticeStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unimod_eta_gramDet_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (x : B.A), B.σ x = x → (B.X x).Nonempty → K.eta (B.gramDet x) = 1 := by
  first | exact @GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one | exact GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one | (intros; apply GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one <;> assumption)
end _root_.GlobalTheory.T
