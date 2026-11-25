-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.FourierTest.beta_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:49:43.955226+00:00
-- url     : https://prove2.me/submissions/38c233f3-1b8e-4bc8-9dab-5f0df5a05941

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive
import Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_beta_symm

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
    (beta A x).IsSymm := LinearMap.BilinForm.isSymm_def.2 (beta_symm A hK hL x)
end GlobalTheory.JR.WeilQuad.FourierTest
