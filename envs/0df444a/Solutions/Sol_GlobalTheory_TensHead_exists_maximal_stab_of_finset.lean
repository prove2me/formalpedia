-- Prove2me | solution 1 for GlobalTheory.TensHead.exists_maximal_stab_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:27:36.556463+00:00
-- url     : https://prove2.me/submissions/b5cbf838-7147-449d-b1f1-d87402236101

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMaximalOperatorStableOfFinsetGenerating

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead
namespace GlobalTheory.TensHead
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V]
    (G : Set (Module.End ℂ V)) (R : Submodule ℂ V) (F : Finset V)
    (hF : ∀ N : Submodule ℂ V, R ≤ N → Stab G N → (↑F : Set V) ⊆ ↑N → N = ⊤) :
    ∀ N : Submodule ℂ V, R ≤ N → Stab G N → N ≠ ⊤ →
      ∃ N' : Submodule ℂ V, N ≤ N' ∧ Stab G N' ∧ N' ≠ ⊤ ∧
        ∀ U : Submodule ℂ V, Stab G U → N' ≤ U → U = N' ∨ U = ⊤ := by
  intro N hRN hN hNtop
  let s : Set (Submodule ℂ V) := {U | R ≤ U ∧ Stab G U ∧ ¬ (↑F : Set V) ⊆ ↑U}
  have hcomp := (CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le _ _).1
    (Submodule.finset_span_isCompactElement (R := ℂ) F)
  have hNs : N ∈ s := ⟨hRN, hN, fun h => hNtop (hF N hRN hN h)⟩
  obtain ⟨M, hNM, hM⟩ := zorn_le_nonempty₀ s (by
    intro c hcs hc y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨le_trans (hcs hy).1 (le_sSup hy), ?_, ?_⟩, fun z hz => le_sSup hz⟩
    · intro g hg x hx
      obtain ⟨U, hU, hxU⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨U, hU, (hcs hU).2.1 g hg x hxU⟩
    · intro hFc
      have hspan : Submodule.span ℂ (↑F : Set V) ≤ sSup c := Submodule.span_le.2 hFc
      obtain ⟨U, hU, hle⟩ := hcomp c hne hdir hspan
      exact (hcs hU).2.2 (Submodule.span_le.1 hle)) N hNs
  refine ⟨M, hNM, hM.prop.2.1, fun h => hM.prop.2.2 (by rw [h]; exact fun _ _ => trivial), ?_⟩
  intro U hU hMU
  by_cases hFU : (↑F : Set V) ⊆ ↑U
  · exact Or.inr (hF U (le_trans hM.prop.1 hMU) hU hFU)
  · exact Or.inl (le_antisymm (hM.2 ⟨le_trans hM.prop.1 hMU, hU, hFU⟩ hMU) hMU)
end GlobalTheory.TensHead
