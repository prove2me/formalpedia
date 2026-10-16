-- Prove2me | solution 1 for OAI.Problem310.FiniteTableModel.outcomeLaw_routed_no_default
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:05:30.809407+00:00
-- url     : https://prove2.me/submissions/bd4b73f8-2d6a-4c4c-895c-88fc5d320bb8

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/RoutedFirstDefault.lean:L10-L32
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.FiniteTableModel.outcomeLaw_routed_no_default. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_FiniteTableModel_measure_center_no_default_prod
import Theorems.Thm_OAI_Problem310_FirstDefault_cylinder_iff_chooseChild
import Theorems.Thm_OAI_Problem310_RoutingPath_noDefault_iff_exists_choices
import Theorems.Thm_OAI_Problem310_RoutingPath_noDefault_iff_not_mem

-- ---- from OAI.MeasureTheory.DyadicAvoidance.FirstDefault ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_Ω

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem310.FirstDefault

lemma pathPrefix_eq_take_ofFn {M d : ℕ} (f : Path M d) (k : Fin d) :
    pathPrefix f k = (List.ofFn fun j => (f j).castSucc).take k.val := by
  exact Fin.ofFn_take_eq_take_ofFn k.isLt.le (fun j => (f j).castSucc)

end Problem310.FirstDefault

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.CenterFirstDefault ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_T

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem310.FiniteTableModel

/-- The survival estimate with all probability measures instantiated, including
the Bernoulli terminal labels in the canonical complete outcome space. -/
theorem outcomeLaw_center_no_default {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    (ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1)
      (⋃ f : FirstDefault.Path M d, {ω : SelectorTable bS × TerminalTable bT |
        ∀ i : FirstDefault.Tests f,
        selectorValue bS ω.1 (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
          FirstDefault.requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  exact measure_center_no_default_prod
    (ConcreteLabels.terminalLaw (TerminalAddress bT) p hp0 hp1)
    bS ConcreteLabels.fairLaw ConcreteLabels.fairLaw_singleton x

end Problem310.FiniteTableModel

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.FirstDefaultSelection ----
namespace OAI

universe u_Ω u_ι u_X u_Y

noncomputable section

namespace Problem310.FirstDefault

/-- The actual routed center avoids the default exactly on the finite union
of the path cylinders used by the exact first-default probability law. -/
theorem noDefault_iff_mem_cylinders {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) (ω : Ω) :
    (∀ k < d, centerChoice S (RoutingPath.routeFrom (centerChoice S) k [] ω) ω ≠
      Fin.last M) ↔ ω ∈ ⋃ f : Path M d, cylinder S f := by
  rw [RoutingPath.noDefault_iff_exists_choices]
  simp only [Set.mem_iUnion, cylinder_iff_chooseChild]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, fun k => ?_⟩
    simpa only [centerChoice, pathPrefix_eq_take_ofFn] using hf k.val k.isLt
  · rintro ⟨f, hf⟩
    refine ⟨f, fun k hk => ?_⟩
    simpa only [centerChoice, pathPrefix_eq_take_ofFn] using hf ⟨k, hk⟩

/-- Change the auxiliary parameter space without changing any node choices. -/
theorem routeFrom_change_parameter {ι : Type u_ι} {X : Type u_X} {Y : Type u_Y}
    (f : List ι → X → ι) (g : List ι → Y → ι) (x : X) (y : Y)
    (h : ∀ P, f P x = g P y) (n : ℕ) (P : List ι) :
    RoutingPath.routeFrom f n P x = RoutingPath.routeFrom g n P y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [RoutingPath.routeFrom_succ, ih, h]

/-- Equivalent leaf-membership formulation, convenient for concrete routers. -/
theorem default_not_mem_iff_mem_cylinders {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) (ω : Ω) :
    Fin.last M ∉ RoutingPath.routeFrom (centerChoice S) d [] ω ↔
      ω ∈ ⋃ f : Path M d, cylinder S f := by
  rw [← RoutingPath.noDefault_iff_not_mem]
  exact noDefault_iff_mem_cylinders S ω

/-- Spatially parametrized selectors have the same no-default event as the
cylinders at a fixed center. This is directly usable with `selectorValue`. -/
theorem spatial_default_not_mem_iff {M d : ℕ} {Ω : Type u_Ω} {X : Type u_X}
    (S : Ω → List (Fin (M + 1)) → Fin M → X → Bool) (ω : Ω) (x : X) :
    Fin.last M ∉ RoutingPath.routeFrom
      (fun P y => OrderedRouting.chooseChild (fun j => S ω P j y)) d [] x ↔
      ω ∈ ⋃ f : Path M d,
        cylinder (fun a ω' => S ω' a.1 a.2 x) f := by
  have hr := routeFrom_change_parameter
    (centerChoice (fun a ω' => S ω' a.1 a.2 x))
    (fun P y => OrderedRouting.chooseChild (fun j => S ω P j y)) ω x
    (fun _ => rfl) d []
  rw [← hr]
  exact default_not_mem_iff_mem_cylinders _ ω

end Problem310.FirstDefault

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutedFirstDefault ----
namespace OAI

noncomputable section

namespace Problem310.FiniteTableModel

/-- Exact no-default probability for the actual depth-`d` spatial router
under the finite selector/terminal outcome law. All randomness is instantiated. -/
theorem outcomeLaw_routed_no_default {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    (ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1)
      {ω : SelectorTable bS × TerminalTable bT |
        Fin.last M ∉ RoutingPath.routeFrom
          (fun P y => OrderedRouting.chooseChild (fun i => selectorValue bS ω.1 P i y))
          d [] x} = (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  have heq : {ω : SelectorTable bS × TerminalTable bT |
        Fin.last M ∉ RoutingPath.routeFrom
          (fun P y => OrderedRouting.chooseChild (fun i => selectorValue bS ω.1 P i y))
          d [] x} =
      ⋃ f : FirstDefault.Path M d, {ω : SelectorTable bS × TerminalTable bT |
        ∀ i : FirstDefault.Tests f,
          selectorValue bS ω.1 (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
            FirstDefault.requiredBit f i} := by
    ext ω
    exact FirstDefault.spatial_default_not_mem_iff
      (fun ω P i y => selectorValue bS ω.1 P i y) ω x
  rw [heq]
  exact outcomeLaw_center_no_default bS bT p hp0 hp1 x

end Problem310.FiniteTableModel

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.FiniteTableModel


theorem solution : type_of% @_root_.OAI.Problem310.FiniteTableModel.outcomeLaw_routed_no_default := @_root_.OAI.Problem310.FiniteTableModel.outcomeLaw_routed_no_default
