-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.FourierTest.beta_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:17.617977+00:00
-- url     : https://prove2.me/submissions/3f48e4d0-c189-4256-88f7-7f48e391b75a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive
import Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_beta_apply
import Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_algMap_inj
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.FourierTest
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilQuad.FourierTest
theorem _root_.solution [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) :
    ∀ a b, beta A x a b = beta A x b a := by
  intro a b
  rw [beta_apply, beta_apply]
  congr 2
  apply algMap_inj A hK hL
  rw [(GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, star_mul, star_mul, star_star, star_star]
  ring
end GlobalTheory.JR.WeilQuad.FourierTest
