-- Prove2me | solution 1 for GlobalTheory.UnitLemma.IntegralFinite.isIntegral_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:11:46.962327+00:00
-- url     : https://prove2.me/submissions/649fd9e5-de1e-4cb4-9c96-5fdcec4f9765

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteIntegralClosureOfSeparableInvolutionAlgebr
import Theorems.Thm_GlobalTheory_UnitLemma_IntegralFinite_isIntegral_matrix_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.IntegralFinite
open Matrix
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.IntegralFinite
theorem _root_.solution {x : B.A} (hx : IsIntegral K.O x) :
    IsIntegral K.O (Algebra.trace K.E B.A x) := by
  let bs := Module.finBasis K.E B.A
  rw [Algebra.trace_eq_matrix_trace bs]
  exact isIntegral_matrix_trace _ (hx.map ((Algebra.leftMulMatrix bs).restrictScalars K.O))
end GlobalTheory.UnitLemma.IntegralFinite
