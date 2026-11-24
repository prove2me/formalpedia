-- Prove2me | solution 1 for GlobalTheory.InertSupp.mem_unipOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:54:35.207193+00:00
-- url     : https://prove2.me/submissions/52ef9b67-f3d2-4b1f-982a-a1d11f1f9fee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_GodementJacquetZeta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix MeasureTheory
open GlobalTheory GlobalTheory.InertSupp
variable {n : Type} [Fintype n] [DecidableEq n]
variable (R : Type) [CommRing R]
variable {R}
open ValuativeRel Matrix MeasureTheory
variable {n : Type} [Fintype n] [DecidableEq n]
variable (R : Type) [CommRing R]
variable {R}
namespace GlobalTheory.InertSupp
namespace _root_.GlobalTheory.InertSupp
theorem _root_.solution {c : n → ℤ} {g : GL n R} :
    g ∈ _root_.GlobalTheory.InertSupp.unipOf R c ↔
      ∀ i j, ¬ c i < c j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j :=
  Iff.rfl
end _root_.GlobalTheory.InertSupp
end GlobalTheory.InertSupp
