-- Prove2me | solution 1 for OAI.Problem310.CenterFailureBound.raw_failure_le_of_center_atoms
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:51:51.774021+00:00
-- url     : https://prove2.me/submissions/ad57ab21-2825-4167-b31f-63dbd93ae82d

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/CenterFailureBound.lean:L28-L62
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.CenterFailureBound.raw_failure_le_of_center_atoms. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_ExposureUnionBound_measure_le_of_finite_exposure

-- ---- from OAI.MeasureTheory.DyadicAvoidance.CenterRouteExposure ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

universe u_ι u_X u_Y

noncomputable section

namespace Problem310.CenterRouteExposure
open Problem310.RoutingPath

/-- Equality of all node decisions at two samples identifies their entire routes,
even when the two decision functions have different parameter spaces. -/
theorem routeFrom_congr_at {ι : Type u_ι} {X : Type u_X} {Y : Type u_Y}
    (chooseX : List ι → X → ι) (chooseY : List ι → Y → ι)
    (x : X) (y : Y) (h : ∀ P, chooseX P x = chooseY P y)
    (n : ℕ) (P : List ι) :
    routeFrom chooseX n P x = routeFrom chooseY n P y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [routeFrom_succ, ih, h]

/-- The decision at every stage is also fixed by the node-decision data. -/
theorem route_decision_congr_at {ι : Type u_ι} {X : Type u_X} {Y : Type u_Y}
    (chooseX : List ι → X → ι) (chooseY : List ι → Y → ι)
    (x : X) (y : Y) (h : ∀ P, chooseX P x = chooseY P y)
    (n : ℕ) (P : List ι) :
    chooseX (routeFrom chooseX n P x) x =
      chooseY (routeFrom chooseY n P y) y := by
  rw [routeFrom_congr_at chooseX chooseY x y h]
  exact h _

open Problem310.FiniteTableModel Problem310.OrderedRouting

/-- Even the extended selector function is fixed by center exposure: invalid
nodes use the same constant false value in both outcomes. -/
theorem selectorValue_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω')
    (P : List (Child M)) (i : Fin M) :
    selectorValue b ω P i x = selectorValue b ω' P i x := by
  by_cases hP : P.length < d
  · have he := congrFun h (⟨P, hP⟩, i)
    simpa only [centerExposure, selectorValue, dite_eq_left hP] using he
  · simp only [selectorValue, dite_eq_right hP]

theorem centerChoice_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω') (P : List (Child M)) :
    centerChoice b x P ω = centerChoice b x P ω' := by
  exact chooseChild_congr _ _ (selectorValue_eq_of_centerExposure_eq b x h P)

/-- The decision made at every center-route stage is constant on the atom. -/
theorem centerRoute_decision_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω')
    (n : ℕ) (P : List (Child M)) :
    centerChoice b x (routeFrom (centerChoice b x) n P ω) ω =
      centerChoice b x (routeFrom (centerChoice b x) n P ω') ω' :=
  route_decision_congr_at _ _ ω ω' (centerChoice_eq_of_centerExposure_eq b x h) n P

/-- The finite-atom good predicate is exactly the actual center-path default event. -/
theorem goodExposure_centerExposure_iff {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ω : SelectorTable b) :
    GoodExposure b x (centerExposure b x ω) ↔
      ∃ k < d, centerChoice b x (routeFrom (centerChoice b x) k [] ω) ω = Fin.last M := by
  have he : centerExposure b x ω = centerExposure b x
      (centerCompletion b x (centerExposure b x ω)) := by simp
  constructor
  · rintro ⟨k, hk, hd⟩
    exact ⟨k, hk, (centerRoute_decision_eq_of_centerExposure_eq b x he k []).trans hd⟩
  · rintro ⟨k, hk, hd⟩
    exact ⟨k, hk, (centerRoute_decision_eq_of_centerExposure_eq b x he k []).symm.trans hd⟩

/-- This is the event identity used to transport the no-default probability
estimate to the bad atoms of the full center-exposure partition. -/
theorem badExposure_centerExposure_iff {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ω : SelectorTable b) :
    ¬ GoodExposure b x (centerExposure b x ω) ↔
      ∀ k < d, centerChoice b x (routeFrom (centerChoice b x) k [] ω) ω ≠ Fin.last M := by
  rw [goodExposure_centerExposure_iff]
  simp only [not_exists, not_and, ne_eq]

end Problem310.CenterRouteExposure

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.CenterFailureBound ----
namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310.CenterFailureBound

open FiniteTableModel CenterRouteExposure

/-- Concrete assembly of the atom bounds into the raw `2p` failure estimate.
All exposure fibers, their measurability, and their total mass are discharged
here for the canonical finite selector/terminal table model. -/
theorem raw_failure_le_of_center_atoms {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (μ : Measure (SelectorTable bS × TerminalTable bT)) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 ≤ p) (B : SelectorTable bS × TerminalTable bT → Set ℝ)
    (N : Set ℕ) (x : ℝ)
    (hbad : μ (noDefaultEvent bS bT x) ≤ ENNReal.ofReal p)
    (hatom : ∀ ξ : Node M d × Fin M → Bool, GoodExposure bS x ξ →
      μ ({ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} ∩
          centerAtom bS bT x ξ) ≤
        ENNReal.ofReal p * μ (centerAtom bS bT x ξ)) :
    μ {ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} ≤
      ENNReal.ofReal (2 * p) := by
  classical
  let f : SelectorTable bS × TerminalTable bT → (Node M d × Fin M → Bool) :=
    fun ω => centerExposure bS x ω.1
  let good : Set (Node M d × Fin M → Bool) := {ξ | GoodExposure bS x ξ}
  have hf (ξ) : MeasurableSet {ω | f ω = ξ} := (Set.to_countable _).measurableSet
  have hbad' : μ {ω | f ω ∉ good} ≤ ENNReal.ofReal p := by
    have heq : {ω | f ω ∉ good} = noDefaultEvent bS bT x := by
      ext ω
      exact badExposure_centerExposure_iff bS x ω.1
    rwa [heq]
  have h := ExposureUnionBound.measure_le_of_finite_exposure μ f hf
    {ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} good
    (ENNReal.ofReal p) (ENNReal.ofReal p) hbad' (fun ξ hξ => hatom ξ hξ)
  calc
    μ {ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)}
        ≤ ENNReal.ofReal p + ENNReal.ofReal p := h
    _ = ENNReal.ofReal (2 * p) := by
      rw [← ENNReal.ofReal_add hp hp]
      congr 1
      ring

end Problem310.CenterFailureBound

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.CenterFailureBound
open Set MeasureTheory
open FiniteTableModel CenterRouteExposure


theorem solution : type_of% @_root_.OAI.Problem310.CenterFailureBound.raw_failure_le_of_center_atoms := @_root_.OAI.Problem310.CenterFailureBound.raw_failure_le_of_center_atoms
