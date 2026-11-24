-- Prove2me | solution 1 for GlobalTheory.UnitLemma.TraceNondeg.minpoly_dvd_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:00:17.564943+00:00
-- url     : https://prove2.me/submissions/acfd4816-fd09-4e71-bd29-fcea7510f516

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TraceNondeg
namespace GlobalTheory.UnitLemma.TraceNondeg
theorem _root_.solution {K : UQ} (B : InvAlg K) : minpoly K.E B.g ∣ B.P := by
  have h1 : minpoly K.E (Algebra.lmul K.E B.A B.g) = minpoly K.E B.g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A) (Algebra.lmul_injective) B.g
  rw [← h1]
  exact LinearMap.minpoly_dvd_charpoly _
end GlobalTheory.UnitLemma.TraceNondeg
