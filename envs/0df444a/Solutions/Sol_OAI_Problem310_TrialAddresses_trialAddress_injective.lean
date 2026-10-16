-- Prove2me | solution 1 for OAI.Problem310.TrialAddresses.trialAddress_injective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:26:42.351093+00:00
-- url     : https://prove2.me/submissions/c1cd94c4-5437-4f21-8b0e-521e4e6a27d5

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/TrialAddresses.lean:L59-L76
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.TrialAddresses.trialAddress_injective. The node keeps its source
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

/-- Distinct table/index pairs give distinct fresh selector coordinates. -/
theorem trialAddress_injective {I : Type u_I} {E : Type u_E} (b : E → ℕ) (edge : I → E)
    (n : I → ℕ) (x t : ℝ) (htlo : 1 ≤ t) (hthi : t ≤ 2)
    (hnlo : ∀ i, 3 ≤ n i) (hnhi : ∀ i, n i ≤ b (edge i))
    (hpair : Function.Injective (fun i => (edge i, n i))) :
    Function.Injective (trialAddress b edge n x t) := by
  intro i j h
  have he : edge i = edge j := congrArg Sigma.fst h
  have hv := congrArg (fun z : GridAddress b => z.2.val) h
  change (dyadicKey (b (edge i)) _).val = (dyadicKey (b (edge j)) _).val at hv
  rw [he] at hv
  have hk : dyadicKey (b (edge j)) (x + t * (2 : ℝ)⁻¹ ^ n i) =
      dyadicKey (b (edge j)) (x + t * (2 : ℝ)⁻¹ ^ n j) := Fin.ext hv
  have hi : n i ≤ b (edge j) := he ▸ hnhi i
  have hn : n i = n j :=
    dyadicKey_injOn (a := 3) (by omega) htlo hthi
      ⟨hnlo i, hi⟩ ⟨hnlo j, hnhi j⟩ hk
  exact hpair (Prod.ext he hn)

end Problem310.TrialAddresses

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.TrialAddresses
open GridSeparation


theorem solution.{u_E,u_I} : type_of% @_root_.OAI.Problem310.TrialAddresses.trialAddress_injective.{u_E,u_I} := @_root_.OAI.Problem310.TrialAddresses.trialAddress_injective.{u_E,u_I}
