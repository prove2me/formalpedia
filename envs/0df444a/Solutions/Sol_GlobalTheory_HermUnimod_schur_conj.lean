-- Prove2me | solution 1 for GlobalTheory.HermUnimod.schur_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:29:28.243414+00:00
-- url     : https://prove2.me/submissions/f3ed0cab-0018-4d4f-9c56-212ef156dc5f

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermUnimod
variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
namespace GlobalTheory.HermUnimod
theorem _root_.solution {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m E) (B : Matrix m Unit E) :
    (fromBlocks 1 0 (-Bᴴ) 1 : Matrix (m ⊕ Unit) (m ⊕ Unit) E)ᴴ * fromBlocks A B Bᴴ 1 *
        fromBlocks 1 0 (-Bᴴ) 1 = fromBlocks (A - B * Bᴴ) 0 0 1 := by
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, sub_eq_add_neg]
end GlobalTheory.HermUnimod
