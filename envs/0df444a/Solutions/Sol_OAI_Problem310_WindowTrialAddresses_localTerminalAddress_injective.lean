-- Prove2me | solution 1 for OAI.Problem310.WindowTrialAddresses.localTerminalAddress_injective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:31:47.378602+00:00
-- url     : https://prove2.me/submissions/51b87a5b-a3a8-4f71-8407-7c1b2dd2c002

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowTrialAddresses.lean:L87-L113
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.WindowTrialAddresses.localTerminalAddress_injective. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Theorems.Thm_OAI_Problem310_TrialAddresses_terminalAddress_injective

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowTableModel ----
namespace OAI

noncomputable section

namespace Problem310.FiniteTableModel

variable {M d g r₀ : ℕ}

lemma selectorEdge_valid (P : Node M d) (i : Fin M) :
    ValidWindowEdge d (selectorEdge P i) := by
  constructor
  · simp [selectorEdge]
  · have hP := P.property
    simp only [selectorEdge, List.length_append, List.length_singleton]
    omega

lemma leaf_valid (hd : 0 < d) (L : Leaf M d) : ValidWindowEdge d L.val := by
  constructor
  · intro h
    have hL := L.property
    rw [h] at hL
    simp only [List.length_nil] at hL
    omega
  · exact le_of_eq L.property

lemma incoming_le_terminalEndpoints
    (W : WindowData (M + 1) d g r₀) (P : Node M d) (i : Fin M) (L : Leaf M d)
    (hprefix : (selectorEdge P i).IsPrefix L.val) :
    selectorEndpoints W P i ≤ terminalEndpoints W L := by
  have hd : 0 < d := by have := P.property; omega
  exact (W.descendant_bounds (selectorEdge P i) L.val
    (selectorEdge_valid P i) (leaf_valid hd L) hprefix).1

lemma selector_window_endpoint
    (W : WindowData (M + 1) d g r₀) (P : Node M d) (i : Fin M) :
    selectorEndpoints W P i + 1 = W.a (selectorEdge P i) + W.r (d - P.val.length) := by
  have h := W.endpoint (selectorEdge P i) (selectorEdge_valid P i)
  simpa [selectorEndpoints, selectorEdge] using h

end Problem310.FiniteTableModel

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.TrialAddresses ----
namespace OAI

universe u_E u_I u_C u_L

noncomputable section

namespace Problem310.TrialAddresses

open GridSeparation

theorem windowTrial_pair_injective {M r : ℕ} {E : Type u_E}
    (a : Fin M → ℕ) (edge : Fin M → E) (hedge : Function.Injective edge) :
    Function.Injective (fun i : WindowTrial M r =>
      (edge i.1, windowTrialIndex a i)) := by
  intro i j h
  have hc : i.1 = j.1 := hedge (congrArg Prod.fst h)
  have hn : windowTrialIndex a i = windowTrialIndex a j := congrArg Prod.snd h
  have ho : i.2 = j.2 := by
    apply Fin.ext
    dsimp [windowTrialIndex] at hn
    rw [hc] at hn
    omega
  exact Prod.ext hc ho

end Problem310.TrialAddresses

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowTrialAddresses ----
namespace OAI

noncomputable section

namespace Problem310.WindowTrialAddresses

open FiniteTableModel TrialAddresses

variable {M d g r₀ : ℕ}

theorem localIndex_bounds (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (z : LocalTrial W P) :
    3 ≤ localIndex W P z ∧ localIndex W P z ≤ selectorEndpoints W P z.1 := by
  have hs := W.start_three (selectorEdge P z.1) (selectorEdge_valid P z.1)
  have he := selector_window_endpoint W P z.1
  have hk := z.2.isLt
  dsimp [localIndex, windowTrialIndex, localStarts]
  omega

/-- Once local routing stays in its chosen child subtree, all terminal
coordinates are distinct. WindowData automatically supplies the necessary
resolution refinement, so no numerical hypothesis remains. -/
theorem localTerminalAddress_injective (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (leaf : LocalTrial W P → Leaf M d)
    (hprefix : ∀ z, (selectorEdge P z.1).IsPrefix (leaf z).val) :
    Function.Injective (fun z : LocalTrial W P =>
      terminalAddress (terminalEndpoints W) (leaf z)
        (x + t * ((2 : ℝ)⁻¹ ^ localIndex W P z))) := by
  change Function.Injective (trialAddress (terminalEndpoints W) leaf (localIndex W P) x t)
  apply TrialAddresses.terminalAddress_injective
    (fun z : LocalTrial W P => z.1) (localIndex W P) leaf
    (selectorEndpoints W P) (terminalEndpoints W) x t ht.1 ht.2
  · exact fun z => (localIndex_bounds W P z).1
  · exact fun z => (localIndex_bounds W P z).2
  · exact fun z => incoming_le_terminalEndpoints W P z.1 (leaf z) (hprefix z)
  · intro i j hij
    have hpath : (leaf i).val = (leaf j).val := congrArg Subtype.val hij
    obtain ⟨si, hsi⟩ := hprefix i
    obtain ⟨sj, hsj⟩ := hprefix j
    have heq : P.val ++ (i.1.castSucc :: si) = P.val ++ (j.1.castSucc :: sj) := by
      simpa only [selectorEdge, List.append_assoc, List.singleton_append] using
        hsi.trans (hpath.trans hsj.symm)
    have hchild := (List.cons.inj (List.append_cancel_left heq)).1
    exact Fin.ext (congrArg (fun v : Fin (M + 1) => v.val) hchild)
  · exact windowTrial_pair_injective (localStarts W P) id (fun _ _ h => h)

end Problem310.WindowTrialAddresses

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.WindowTrialAddresses
open FiniteTableModel TrialAddresses


theorem solution : type_of% @_root_.OAI.Problem310.WindowTrialAddresses.localTerminalAddress_injective := @_root_.OAI.Problem310.WindowTrialAddresses.localTerminalAddress_injective
