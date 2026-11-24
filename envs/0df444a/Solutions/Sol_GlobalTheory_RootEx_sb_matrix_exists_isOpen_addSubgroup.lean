-- Prove2me | solution 1 for GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:05.629978+00:00
-- url     : https://prove2.me/submissions/64dd1d8e-d658-483c-9b70-a526cc8d8d90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Theorems.Thm_GlobalTheory_RootEx_exists_isOpen_addSubgroup_add_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
open GlobalTheory GlobalTheory.RootEx
open MeasureTheory ValuativeRel Matrix
open scoped Topology Pointwise
namespace GlobalTheory.RootEx
namespace _root_.GlobalTheory.RootEx
theorem _root_.solution :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (a b : Type) [Fintype a] [Fintype b], ∀ Φ ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix a b k),
      ∃ Λ : AddSubgroup (Matrix a b k), IsOpen (Λ : Set (Matrix a b k)) ∧
        ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  intro k _ _ _ _ a b _ _ Φ hΦ
  obtain ⟨hlc, hcs⟩ := hΦ
  exact _root_.GlobalTheory.RootEx.exists_isOpen_addSubgroup_add_eq hlc hcs
end _root_.GlobalTheory.RootEx
end GlobalTheory.RootEx
