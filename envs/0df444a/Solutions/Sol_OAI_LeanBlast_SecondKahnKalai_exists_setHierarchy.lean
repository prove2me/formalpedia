-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.exists_setHierarchy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:27:07.067493+00:00
-- url     : https://prove2.me/submissions/1b9a4fcd-456e-4c78-9cca-813e1eb82b89

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/GraphHierarchy.lean:L80-L138
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.exists_setHierarchy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy

-- ---- from OAI.Combinatorics.GraphThreshold.GraphHierarchy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! The finite hierarchy and the actual tree of extensions used in the graph
application. Histories are represented by the probability tree's dependent
paths; equal set labels do not identify distinct histories. -/

noncomputable section

open Finset

namespace LeanBlast.SecondKahnKalai

namespace SetHierarchy

variable {X : Type*} [DecidableEq X]
variable {R : Finset X → Finset X → Prop} {H : Finset X}

end SetHierarchy

/-- Strict cardinal descent constructs a finite hierarchy; no chain or tree is
assumed as an input. The predecessor hypotheses are needed only inside `H`. -/
theorem exists_setHierarchy {X : Type*} [DecidableEq X]
    (R : Finset X → Finset X → Prop) (H : Finset X)
    (hpred : ∀ I, I ⊆ H → I.Nonempty →
      ∃ S, S ⊆ I ∧ 17 * S.card < I.card ∧ R S I) :
    Nonempty (SetHierarchy R H) := by
  have aux : ∀ m : ℕ, ∀ I : Finset X, I.card = m → I ⊆ H →
      Nonempty (SetHierarchy R I) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro I hcard hIH
      by_cases hI : I = ∅
      · subst I
        exact ⟨{
          depth := 0
          stage := fun _ => ∅
          first := rfl
          last := rfl
          nested := by omega
          sparse := by omega
          selected := by omega }⟩
      · obtain ⟨S, hSI, hsmall, hRSI⟩ := hpred I hIH (Finset.nonempty_iff_ne_empty.mpr hI)
        have hlt : S.card < m := by omega
        obtain ⟨a⟩ := ih S.card hlt S rfl (hSI.trans hIH)
        refine ⟨{
          depth := a.depth + 1
          stage := fun i => if i ≤ a.depth then a.stage i else I
          first := by simpa using a.first
          last := by simp
          nested := ?_
          sparse := ?_
          selected := ?_ }⟩
        · intro i hi
          by_cases hik : i < a.depth
          · simpa only [ite_eq_left (show i ≤ a.depth by omega),
              ite_eq_left (show i + 1 ≤ a.depth by omega)] using a.nested i hik
          · have hik' : i = a.depth := by omega
            subst i
            simpa only [ite_eq_left (le_refl a.depth),
              ite_eq_right (show ¬a.depth + 1 ≤ a.depth by omega), a.last] using hSI
        · intro i hi
          by_cases hik : i < a.depth
          · simpa only [ite_eq_left (show i ≤ a.depth by omega),
              ite_eq_left (show i + 1 ≤ a.depth by omega)] using a.sparse i hik
          · have hik' : i = a.depth := by omega
            subst i
            simpa only [ite_eq_left (le_refl a.depth),
              ite_eq_right (show ¬a.depth + 1 ≤ a.depth by omega), a.last] using hsmall
        · intro i hi
          by_cases hik : i < a.depth
          · simpa only [ite_eq_left (show i ≤ a.depth by omega),
              ite_eq_left (show i + 1 ≤ a.depth by omega)] using a.selected i hik
          · have hik' : i = a.depth := by omega
            subst i
            simpa only [ite_eq_left (le_refl a.depth),
              ite_eq_right (show ¬a.depth + 1 ≤ a.depth by omega), a.last] using hRSI
  exact aux H.card H rfl Subset.rfl

section OrbitTrees

variable (G : Type*) [Group G] [Fintype G]
variable {X : Type} [DecidableEq X] [MulAction G X]

end OrbitTrees

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.exists_setHierarchy := @_root_.OAI.LeanBlast.SecondKahnKalai.exists_setHierarchy
