-- Prove2me | solution 1 for GlobalTheory.RootEx.Supp.exists_bd_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:51.027712+00:00
-- url     : https://prove2.me/submissions/db16d171-a3ca-41c3-8435-05dcd6a11480

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball


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
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Supp
variable {k : Type} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.Supp
theorem _root_.solution {ι κ : Type} [Finite ι] [Finite κ] {S : Set (Matrix ι κ k)} (hS : IsCompact S) :
    ∃ γ : ValueGroupWithZero k, ∀ x ∈ S, Bd γ x := by
  have hT : IsCompact (⋃ r, ⋃ s, (fun x : Matrix ι κ k => x r s) '' S) :=
    isCompact_iUnion fun r => isCompact_iUnion fun s => hS.image (by fun_prop)
  obtain ⟨u, hu⟩ := hT.elim_directed_cover (fun s : kˣ => cball s) isOpen_cball
    (fun y _ => by
      by_cases hy : y = 0
      · exact Set.mem_iUnion.2 ⟨1, by simp [cball, hy]⟩
      · exact Set.mem_iUnion.2 ⟨Units.mk0 y hy, by simp [cball]⟩)
    (fun s t => by
      rcases le_total (valuation k (s : k)) (valuation k (t : k)) with h | h
      · exact ⟨t, fun y (hy : valuation k y ≤ _) => (hy.trans h : valuation k y ≤ _), subset_rfl⟩
      · exact ⟨s, subset_rfl, fun y (hy : valuation k y ≤ _) => (hy.trans h : valuation k y ≤ _)⟩)
  exact ⟨valuation k (u : k), fun x hx r s => hu (Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨s, x, hx, rfl⟩⟩)⟩
end GlobalTheory.RootEx.Supp
