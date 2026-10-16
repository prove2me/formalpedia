-- Prove2me | solution 1 for OAI.Problem310.FiniteLocalPredicate.finite_local_predicate_factors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:07:02.019313+00:00
-- url     : https://prove2.me/submissions/2295692b-8aaf-451c-b05c-a1cf6fe7debe

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/FiniteLocalPredicate.lean:L38-L76
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.FiniteLocalPredicate.finite_local_predicate_factors. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_GridSeparation_periodicKey_dyadic_refine

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridSeparation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α

noncomputable section

namespace Problem310.GridSeparation

lemma periodicKey_dyadic_eq_of_refine {b B : ℕ} {x y : ℝ} (hb : b ≤ B)
    (heq : periodicKey ((2 : ℝ) ^ (B + 2)) x =
      periodicKey ((2 : ℝ) ^ (B + 2)) y) :
    periodicKey ((2 : ℝ) ^ (b + 2)) x =
      periodicKey ((2 : ℝ) ^ (b + 2)) y := by
  rw [periodicKey_dyadic_refine hb x, periodicKey_dyadic_refine hb y, heq]

end Problem310.GridSeparation

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutingPath ----
namespace OAI

universe u_ι u_X

noncomputable section

namespace Problem310.RoutingPath

variable {ι : Type u_ι} {X : Type u_X}

/-- Every routed node extends the starting node. -/
theorem prefix_routeFrom (choose : List ι → X → ι)
    (n : ℕ) (P : List ι) (x : X) : P.IsPrefix (routeFrom choose n P x) := by
  induction n with
  | zero => exact List.prefix_refl _
  | succ n ih =>
      exact ih.trans (List.prefix_append _ _)

end Problem310.RoutingPath

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.LocalPredicateFactor ----
namespace OAI

universe u_ι u_X u_K u_V u_J

noncomputable section

namespace Problem310.LocalPredicateFactor

open RoutingPath GridSeparation

variable {ι : Type u_ι} {X : Type u_X} {K : Type u_K} {V : Type u_V}

/-- Routing through a subtree only uses its strict-descendant choices.
If those choices factor through one key, the terminal leaf does too. -/
theorem route_eq_of_key_eq (choose : List ι → X → ι)
    (key : X → K) (r : ℕ) (P : List ι)
    (hchoice : ∀ Q : List ι, P.IsPrefix Q → Q.length < P.length + r →
      ∀ x y : X, key x = key y → choose Q x = choose Q y)
    {x y : X} (hxy : key x = key y) :
    routeFrom choose r P x = routeFrom choose r P y := by
  apply routeFrom_eq_of_choices_eq choose r P y x
  intro k hk
  apply hchoice (routeFrom choose k P y) (prefix_routeFrom choose k P y)
  · rw [length_routeFrom]
    omega
  · exact hxy

/-- A single table evaluated at any coarser grid is a function of the finest key. -/
theorem table_eq_of_finest_key {b B : ℕ} (hb : b ≤ B)
    (table : Fin (2 ^ (b + 2)) → V) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    table (dyadicKey b x) = table (dyadicKey b y) := by
  apply congrArg table
  apply (dyadicKey_eq_iff b x y).mpr
  exact periodicKey_dyadic_eq_of_refine hb hxy

variable {J : Type u_J}

end Problem310.LocalPredicateFactor

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.FiniteLocalPredicate ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section

namespace Problem310.FiniteLocalPredicate

open RoutingPath GridSeparation LocalPredicateFactor FiniteTableModel

variable {M d : ℕ}

/-- Table lookup at a valid node depends only on a finer common grid. -/
theorem selector_lookup_eq {b : Node M d → Fin M → ℕ} (ω : SelectorTable b)
    (Q : Node M d) (i : Fin M) {B : ℕ} (hb : b Q i ≤ B) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    ω (selectorAddress b Q i x) = ω (selectorAddress b Q i y) := by
  exact table_eq_of_finest_key hb (fun k => ω ⟨(Q, i), k⟩) hxy

/-- The analogous statement for an actual dependent terminal-table address. -/
theorem terminal_lookup_eq {b : Leaf M d → ℕ} (ω : TerminalTable b)
    (L : Leaf M d) {B : ℕ} (hb : b L ≤ B) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    ω (terminalAddress b L x) = ω (terminalAddress b L y) := by
  exact table_eq_of_finest_key hb (fun k => ω ⟨L, k⟩) hxy

/-- Concrete local terminal predicates in the finite table model factor through
the largest resolution in the child subtree. `rule` may be the canonical
first-success/default rule; no assumptions on that rule are needed. -/
theorem finite_local_predicate_factors
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ωS : SelectorTable bS) (ωT : TerminalTable bT)
    (choose : List (Child M) → ℝ → Child M)
    (rule : List (Child M) → (Fin M → Bool) → Child M)
    (hchoose : ∀ Q x, choose Q x = rule Q (fun i => selectorValue bS ωS Q i x))
    (r : ℕ) (P : List (Child M)) (hdepth : P.length + r = d)
    (U : Node M d) (i : Fin M) (B : ℕ)
    (hbS : ∀ Q : Node M d, P.IsPrefix Q.val → ∀ j, bS Q j ≤ B)
    (hbT : ∀ L : Leaf M d, P.IsPrefix L.val → bT L ≤ B)
    (hIn : bS U i ≤ B) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    (ωS (selectorAddress bS U i x) &&
      ωT (terminalAddress bT (localLeaf choose r P hdepth x) x)) =
    (ωS (selectorAddress bS U i y) &&
      ωT (terminalAddress bT (localLeaf choose r P hdepth y) y)) := by
  have hchoice : ∀ Q : List (Child M), P.IsPrefix Q → Q.length < P.length + r →
      ∀ u v : ℝ, ⌊(2 : ℝ) ^ (B + 2) * Int.fract u⌋ =
        ⌊(2 : ℝ) ^ (B + 2) * Int.fract v⌋ → choose Q u = choose Q v := by
    intro Q hPQ hlen u v huv
    have hQ : Q.length < d := hlen.trans_eq hdepth
    rw [hchoose Q u, hchoose Q v]
    apply congrArg (rule Q)
    funext j
    have hlook := selector_lookup_eq ωS (⟨Q, hQ⟩ : Node M d) j
      (hbS ⟨Q, hQ⟩ hPQ j) huv
    simpa only [selectorValue, dite_eq_left hQ] using hlook
  have hroute := route_eq_of_key_eq choose
    (fun z : ℝ => ⌊(2 : ℝ) ^ (B + 2) * Int.fract z⌋) r P hchoice hxy
  have hleaf : localLeaf choose r P hdepth x = localLeaf choose r P hdepth y :=
    Subtype.ext hroute
  have hprefix : P.IsPrefix (localLeaf choose r P hdepth y).val :=
    prefix_routeFrom choose r P y
  rw [selector_lookup_eq ωS U i hIn hxy, hleaf,
    terminal_lookup_eq ωT (localLeaf choose r P hdepth y) (hbT _ hprefix) hxy]

end Problem310.FiniteLocalPredicate

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.FiniteLocalPredicate
open RoutingPath GridSeparation FiniteTableModel


theorem solution : type_of% @_root_.OAI.Problem310.FiniteLocalPredicate.finite_local_predicate_factors := @_root_.OAI.Problem310.FiniteLocalPredicate.finite_local_predicate_factors
