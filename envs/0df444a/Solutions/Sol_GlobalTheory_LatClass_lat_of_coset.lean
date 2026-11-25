-- Prove2me | solution 1 for GlobalTheory.LatClass.lat_of_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:44.938249+00:00
-- url     : https://prove2.me/submissions/3238eec8-4ec4-4808-b501-c7d0910c83e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsValuationEqZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MulMemOfHatCosetIndNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatNeZeroOfMemR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeClasses
import Theorems.Thm_GlobalTheory_LatClass_latOf_eq_of_KO
import Theorems.Thm_GlobalTheory_LatClass_latOf_mul_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.LatClass
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {J : Subgroup (GL (n ⊕ Fin c) k)}
    (hJ : J ≤ KO k _) {a b : GL (n ⊕ Fin c) k}
    (h : DoubleCoset.mk (R k n c 1) J a = DoubleCoset.mk (R k n c 1) J b) :
    ∃ r ∈ R k n c 1, latOf b = latOf (r * a) := by
  obtain ⟨r, hr, w, hw, rfl⟩ := (DoubleCoset.eq _ _ _ _).1 h
  exact ⟨r, hr, by rw [latOf_mul_congr _ (latOf_eq_of_KO (hJ hw)), mul_one]⟩
end GlobalTheory.LatClass
