-- Prove2me | solution 1 for OAI.Problem310.TrialAddresses.terminalAddress_injective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:28:34.112656+00:00
-- url     : https://prove2.me/submissions/13c31f09-270c-49dd-bbbb-fce0ef13adf7

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/TrialAddresses.lean:L78-L104
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.TrialAddresses.terminalAddress_injective. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_GridSeparation_periodicKey_dyadic_ne_of_lt
import Theorems.Thm_OAI_Problem310_GridSeparation_periodicKey_dyadic_refine

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridSeparation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α

noncomputable section

namespace Problem310.GridSeparation

lemma periodicKey_dyadic_injOn {a b : ℕ} {x t : ℝ} (ha : 3 ≤ a)
    (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    Set.InjOn (fun n : ℕ =>
      periodicKey ((2 : ℝ) ^ (b + 2)) (x + t * (2 : ℝ)⁻¹ ^ n))
      (Set.Icc a b) := by
  intro n hn m hm heq
  rcases lt_trichotomy n m with hlt | heq' | hgt
  · exact False.elim ((periodicKey_dyadic_ne_of_lt
      (le_trans ha hn.1) hlt hm.2 htlo hthi) heq)
  · exact heq'
  · exact False.elim ((periodicKey_dyadic_ne_of_lt
      (le_trans ha hm.1) hgt hn.2 htlo hthi) heq.symm)

lemma periodicKey_dyadic_eq_of_refine {b B : ℕ} {x y : ℝ} (hb : b ≤ B)
    (heq : periodicKey ((2 : ℝ) ^ (B + 2)) x =
      periodicKey ((2 : ℝ) ^ (B + 2)) y) :
    periodicKey ((2 : ℝ) ^ (b + 2)) x =
      periodicKey ((2 : ℝ) ^ (b + 2)) y := by
  rw [periodicKey_dyadic_refine hb x, periodicKey_dyadic_refine hb y, heq]

lemma dyadicKey_injOn {a b : ℕ} {x t : ℝ} (ha : 3 ≤ a)
    (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    Set.InjOn (fun n : ℕ => dyadicKey b (x + t * (2 : ℝ)⁻¹ ^ n))
      (Set.Icc a b) := by
  intro n hn m hm heq
  apply periodicKey_dyadic_injOn ha htlo hthi hn hm
  exact (dyadicKey_eq_iff b _ _).mp heq

end Problem310.GridSeparation

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.TrialAddresses ----
namespace OAI

universe u_E u_I u_C u_L

noncomputable section

namespace Problem310.TrialAddresses

open GridSeparation

/-- Refinement preserves all equalities needed to recover a coarse key. -/
theorem dyadicKey_eq_of_refine {b B : ℕ} {x y : ℝ} (hb : b ≤ B)
    (h : dyadicKey B x = dyadicKey B y) : dyadicKey b x = dyadicKey b y := by
  rw [dyadicKey_eq_iff]
  exact periodicKey_dyadic_eq_of_refine hb ((dyadicKey_eq_iff B x y).mp h)

/-- Adaptive terminal addresses are injective whenever equal leaves force
the same child subtree, and each terminal resolution refines that child's
incoming grid. The leaf selection may otherwise depend arbitrarily on all
selector tables. -/
theorem terminalAddress_injective {I : Type u_I} {C : Type u_C} {L : Type u_L}
    (child : I → C) (n : I → ℕ) (leaf : I → L)
    (b : C → ℕ) (B : L → ℕ) (x t : ℝ)
    (htlo : 1 ≤ t) (hthi : t ≤ 2)
    (hnlo : ∀ i, 3 ≤ n i) (hnhi : ∀ i, n i ≤ b (child i))
    (hrefine : ∀ i, b (child i) ≤ B (leaf i))
    (hbranch : ∀ i j, leaf i = leaf j → child i = child j)
    (hpair : Function.Injective (fun i => (child i, n i))) :
    Function.Injective (trialAddress B leaf n x t) := by
  intro i j h
  have hl : leaf i = leaf j := congrArg Sigma.fst h
  have hc : child i = child j := hbranch i j hl
  have hv := congrArg (fun z : GridAddress B => z.2.val) h
  change (dyadicKey (B (leaf i)) _).val = (dyadicKey (B (leaf j)) _).val at hv
  rw [hl] at hv
  have hk : dyadicKey (B (leaf j)) (x + t * (2 : ℝ)⁻¹ ^ n i) =
      dyadicKey (B (leaf j)) (x + t * (2 : ℝ)⁻¹ ^ n j) := Fin.ext hv
  have hcoarse := dyadicKey_eq_of_refine (hrefine j) hk
  have hi : n i ≤ b (child j) := hc ▸ hnhi i
  have hn : n i = n j :=
    dyadicKey_injOn (a := 3) (by omega) htlo hthi
      ⟨hnlo i, hi⟩ ⟨hnlo j, hnhi j⟩ hcoarse
  exact hpair (Prod.ext hc hn)

end Problem310.TrialAddresses

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.TrialAddresses
open GridSeparation


theorem solution.{u_I,u_C,u_L} : type_of% @_root_.OAI.Problem310.TrialAddresses.terminalAddress_injective.{u_I,u_C,u_L} := @_root_.OAI.Problem310.TrialAddresses.terminalAddress_injective.{u_I,u_C,u_L}
