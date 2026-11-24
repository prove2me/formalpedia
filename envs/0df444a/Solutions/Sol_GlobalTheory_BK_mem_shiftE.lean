-- Prove2me | solution 1 for GlobalTheory.BK.mem_shiftE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:54:24.598206+00:00
-- url     : https://prove2.me/submissions/b9314920-a17f-435a-881a-5f2ad8209eb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {R : Type} [Semiring R] [Module R (Vec K a ι)] [SMulCommClass R K⟦X⟧ (Vec K a ι)]
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.BK
theorem _root_.solution {i : ℤ} {W : Submodule R (Vec K a ι)} {y : Vec K a ι} :
    y ∈ shiftE l e i W ↔ Ezpow K l e (-i) • y ∈ W := Iff.rfl
end GlobalTheory.BK
