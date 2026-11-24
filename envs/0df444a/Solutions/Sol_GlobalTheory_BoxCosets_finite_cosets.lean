-- Prove2me | solution 1 for GlobalTheory.BoxCosets.finite_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:11:49.460469+00:00
-- url     : https://prove2.me/submissions/4698e544-60aa-41f0-8daa-d4a4b58bc5c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteQuotientCosetsScaledStandardLatticeBox
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_cball
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.BoxCosets
namespace GlobalTheory.BoxCosets
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (c₁ c₂ : kˣ) :
    {yb : (n → k) ⧸ box n c₂ | ∃ y ∈ box n c₁, Submodule.Quotient.mk y = yb}.Finite := by
  have e : ∀ c : kˣ, (box n c : Set (n → k)) = Set.pi Set.univ (fun _ => cball c) := by
    intro c
    ext y
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    rfl
  have hc : IsCompact (box n c₁ : Set (n → k)) := by
    rw [e]; exact isCompact_univ_pi fun _ => isCompact_cball c₁
  have ho : IsOpen (box n c₂ : Set (n → k)) := by
    rw [e]; exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball c₂
  obtain ⟨t, -, ht⟩ := hc.elim_nhds_subcover
    (fun x => (fun y => y - x) ⁻¹' (box n c₂ : Set (n → k))) (by
      intro x _
      refine (ho.preimage (continuous_id.sub continuous_const)).mem_nhds ?_
      simp)
  refine (t.finite_toSet.image (fun x => (Submodule.Quotient.mk x : (n → k) ⧸ box n c₂))).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  have := ht hy
  simp only [Set.mem_iUnion] at this
  obtain ⟨x, hx, hxy⟩ := this
  exact ⟨x, hx, ((Submodule.Quotient.eq _).2 hxy).symm⟩
end GlobalTheory.BoxCosets
