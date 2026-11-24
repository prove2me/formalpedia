-- Prove2me | solution 1 for GlobalTheory.UnitLemma.PairClass.aeval_mulLeft_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:58:57.197832+00:00
-- url     : https://prove2.me/submissions/b94e0a0e-585f-4988-b972-86d94b388d22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfSeparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PairClass
namespace GlobalTheory.UnitLemma.PairClass
theorem _root_.solution {F A : Type} [Field F] [CommRing A] [Algebra F A] (a : A) (p : F[X]) (z : A) :
    aeval (LinearMap.mulLeft F a) p z = aeval a p * z := by
  have h1 : aeval (Algebra.lmul F A a) p = Algebra.lmul F A (aeval a p) :=
    aeval_algHom_apply (Algebra.lmul F A) a p
  have h2 : Algebra.lmul F A a = LinearMap.mulLeft F a := rfl
  rw [← h2, h1]
  rfl
end GlobalTheory.UnitLemma.PairClass
