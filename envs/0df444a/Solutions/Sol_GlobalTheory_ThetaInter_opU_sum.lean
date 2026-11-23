-- Prove2me | solution 1 for GlobalTheory.ThetaInter.opU_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:32.091806+00:00
-- url     : https://prove2.me/submissions/dd8e3efb-8c11-4d8b-9f6a-76faacf640bd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
namespace GlobalTheory.ThetaInter
theorem _root_.solution {ι : Type*} (s : Finset ι) (x : V) (F : ι → V → ℂ) (z : V) :
    opU H x (fun w => ∑ i ∈ s, F i w) z = ∑ i ∈ s, opU H x (F i) z := by
  simp only [opU, Finset.sum_mul]
end GlobalTheory.ThetaInter
