-- Prove2me | solution 1 for GlobalTheory.JR.EtInv.trace_mul_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:58:44.808845+00:00
-- url     : https://prove2.me/submissions/20f6c7a4-6a7f-4f17-bfd9-f5ec0a5d4f29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtInv
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] [Module.Finite F K]
variable {r : ℕ} {τ : K}
namespace GlobalTheory.JR.EtInv
theorem _root_.solution (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ)) (x a : K) :
    Algebra.trace F K (x * a) = ∑ j, bb.repr x j * Algebra.trace F K (τ ^ (j : ℕ) * a) := by
  conv_lhs => rw [← bb.sum_repr x]
  simp [Finset.sum_mul, smul_mul_assoc, map_sum, hb]
end GlobalTheory.JR.EtInv
