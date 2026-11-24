-- Prove2me | solution 1 for GlobalTheory.UnitLemma.IntegralFinite.trace_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:22:10.570534+00:00
-- url     : https://prove2.me/submissions/659ecda4-3860-4ab5-b286-d13d410c29ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteIntegralClosureOfSeparableInvolutionAlgebr
import Theorems.Thm_GlobalTheory_UnitLemma_IntegralFinite_isIntegral_trace

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
    ∃ c : K.O, algebraMap K.O K.E c = Algebra.trace K.E B.A x :=
  IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_trace B hx)
end GlobalTheory.UnitLemma.IntegralFinite
