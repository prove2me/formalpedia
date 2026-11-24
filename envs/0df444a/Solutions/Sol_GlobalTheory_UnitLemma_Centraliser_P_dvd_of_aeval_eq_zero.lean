-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Centraliser.P_dvd_of_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:02:59.340518+00:00
-- url     : https://prove2.me/submissions/248ccea9-44dc-405f-9497-79c6fb8d71ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_charpoly_dvd_pow_of_aeval_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Centraliser
namespace GlobalTheory.UnitLemma.Centraliser
theorem _root_.solution {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (p : K.E[X])
    (hp : aeval B.g p = 0) : B.P ∣ p := by
  have h1 : aeval (Algebra.lmul K.E B.A B.g) p = 0 := by
    rw [aeval_algHom_apply, hp, map_zero]
  let bs := Module.finBasis K.E B.A
  have h2 : aeval (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul K.E B.A B.g)) p = 0 := by
    rw [aeval_algHom_apply, h1, map_zero]
  have h3 := charpoly_dvd_pow_of_aeval_eq_zero _ p h2
  have h4 : (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul K.E B.A B.g)).charpoly = B.P := by
        exact LinearMap.charpoly_toMatrix _ bs
  rw [h4] at h3
  exact hsep.squarefree.isRadical _ _ h3
end GlobalTheory.UnitLemma.Centraliser
