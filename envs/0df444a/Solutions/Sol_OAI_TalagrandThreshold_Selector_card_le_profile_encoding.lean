-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.card_le_profile_encoding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:40:38.288271+00:00
-- url     : https://prove2.me/submissions/48d13a67-9d7c-4e42-a09c-4336771a1647

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingEncodingBound.lean:L66-L89
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.card_le_profile_encoding. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWords
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWordsTransport
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingRows
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorProfile
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingBound
import Theorems.Thm_OAI_TalagrandThreshold_Selector_coloring_eq_of_movedRows
import Theorems.Thm_OAI_TalagrandThreshold_card_rowEncoding

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorCountingEncoding ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

/-!
# Reconstruction from the actual changed rows

For an earlier coloring, every point outside the changed rows retains its final
color. Inside a changed row its original color is recorded. Thus the changed
subsets and their original labels determine the entire original coloring.
-/

noncomputable section

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

/-- The literal row encoding is injective on originals moved only earlier. -/
theorem rawRowEncoding_injective
    {a b z : Coloring α s} (ha : Earlier a z) (hb : Earlier b z)
    (he : ∀ i, rawRowEncoding a z i = rawRowEncoding b z i) : a = b := by
  have hrows : ∀ i, movedRow a z i = movedRow b z i :=
    fun i => congrArg Sigma.fst (he i)
  apply coloring_eq_of_movedRows ha hb hrows
  intro i x hx
  have hx' : x ∈ movedRow b z i := by rw [← hrows i]; exact hx
  have hlookup := congrArg (fun E => rawRowLookup E x) (he i)
  dsimp only [rawRowLookup, rawRowEncoding] at hlookup
  simp only [dite_eq_left hx, dite_eq_left hx'] at hlookup
  exact Option.some.inj hlookup

end TalagrandThreshold.Selector

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorCountingEncodingBound ----
namespace OAI

/-!
# The fixed-profile encoding bound

Each actual coloring maps to the tuple of its changed row subsets and the
original colors on them. Reconstruction proves this map injective. The row
record permits arbitrary subsets of the fixed ambient sets, so overlap between
those ambient sets can only enlarge the number of records.
-/

noncomputable section
open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

/-- Count actual originals of a fixed final coloring and profile. Every
injectivity and histogram condition is proved from the actual row encoding. -/
theorem card_le_profile_encoding
    (G : Finset (Coloring α s)) (z : Coloring α s) (n : Profile s)
    (R : Fin s → Finset α)
    (hEarlier : ∀ a ∈ G, Earlier a z)
    (hprofile : ∀ a ∈ G, profile a z = n)
    (hrows : ∀ a ∈ G, ∀ i, movedRow a z i ⊆ R i) :
    G.card ≤ ∏ i : Fin s,
      Nat.choose (R i).card (rowCount n i) * wordCount (rowCount n i) (n i) := by
  classical
  let encode : ↥G → ∀ i : Fin s, RowEncoding (R i) (rowCount n i) (n i) :=
    fun a => profileRowEncoding a.val z n R
      (hprofile a.val a.property) (hrows a.val a.property)
  have hinj : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    apply rawRowEncoding_injective
      (hEarlier a.val a.property) (hEarlier b.val b.property)
    intro i
    have hi := congrArg (fun f => rowEncodingForget (f i)) hab
    simpa only [encode, rowEncodingForget_profileRowEncoding] using hi
  have hcard := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_coe, Fintype.card_pi, card_rowEncoding] using hcard

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.card_le_profile_encoding := @_root_.OAI.TalagrandThreshold.Selector.card_le_profile_encoding
