-- Prove2me | solution 1 for GlobalTheory.finite_units_quot_sq_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:58:53.876738+00:00
-- url     : https://prove2.me/submissions/6b847694-9661-4f27-9dec-308fa2e438c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitsQuotSqFiniteEtaleHermitianPair
import Theorems.Thm_GlobalTheory_finite_units_quot_sq_normed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (L : Type) [Field L] [Algebra F L] [Module.Finite F L] :
    Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  classical
  let b := Module.finBasis F L
  let : NormedRing (Matrix (Fin (Module.finrank F L)) (Fin (Module.finrank F L)) F) :=
    Matrix.linftyOpNormedRing
  let : NormedAlgebra F (Matrix (Fin (Module.finrank F L)) (Fin (Module.finrank F L)) F) :=
    Matrix.linftyOpNormedAlgebra
  let N : NormedCommRing L := NormedCommRing.induced L _ (Algebra.leftMulMatrix b)
    (Algebra.leftMulMatrix_injective b)
  let A : @NormedAlgebra F L _ N.toNormedRing.toSeminormedRing :=
    NormedAlgebra.induced F L _ (Algebra.leftMulMatrix b)
  exact @finite_units_quot_sq_normed F _ _ _ _ L N inferInstance A ‹_› (fun x hx => hx.isUnit)
end GlobalTheory
