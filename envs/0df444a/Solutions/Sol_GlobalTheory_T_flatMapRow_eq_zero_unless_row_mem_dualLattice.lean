-- Prove2me | solution 1 for GlobalTheory.T.flatMapRow_eq_zero_unless_row_mem_dualLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:37:54.663496+00:00
-- url     : https://prove2.me/submissions/6156fa60-a321-460a-97c8-73fe17696098

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapRowEqZeroUnlessRowMemDualLattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapRowEqZeroUnlessRowMemDualLatticeStatement
import Theorems.Thm_GlobalTheory_LocFlat_flRow_eq_zero_of_not_mem_box


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Unit) (XIx (Fin κ) t j) k, x (Sum.inr ()) ∉ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1)) → GlobalTheory.LocFlat.flRow S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x = 0 := by
  first | exact @GlobalTheory.LocFlat.flRow_eq_zero_of_not_mem_box | exact GlobalTheory.LocFlat.flRow_eq_zero_of_not_mem_box | (intros; apply GlobalTheory.LocFlat.flRow_eq_zero_of_not_mem_box <;> assumption)
end _root_.GlobalTheory.T
