-- Prove2me | solution 1 for OAI.Problem310.dyadic_affine_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:32:00.536224+00:00
-- url     : https://prove2.me/submissions/418bf15e-7114-496a-9914-56ab66984795

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/Main.lean:L103-L105
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Problem310.dyadic_affine_avoidance.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Problem310_dyadic_affine_avoidance) verbatim and is proved by it.
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridGeometry
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridMeasure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridStability
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowPlacement
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowRecursion
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PackedWindowSpan
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreePreorder
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreePreorderRank
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PreorderIndex
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowSpanSum
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreeSpanBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowDataExistence
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowMetadata
import Theorems.Thm_OAI_Problem310Support_avoidance_of_periodic_hitting
import Theorems.Thm_OAI_Problem310_CenterFailureBound_raw_failure_le_of_center_atoms
import Theorems.Thm_OAI_Problem310_ConcreteWindowAtom_raw_failure_on_good_atom
import Theorems.Thm_OAI_Problem310_Construction_periodic_hitting_of_window_failure
import Theorems.Thm_OAI_Problem310_FiniteTableModel_outcomeLaw_routed_no_default
import Theorems.Thm_OAI_Problem310_RoutingBudget_exists_nondefault_parameters
import Theorems.Thm_OAI_Problem310_RoutingPath_noDefault_iff_not_mem
import Theorems.Thm_OAI_Problem310_exists_windowData_selector_stability

-- ---- from OAI.MeasureTheory.DyadicAvoidance.CenterRouteExposure ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

open Problem310.FiniteTableModel Problem310.OrderedRouting

end Problem310.CenterRouteExposure

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutedExposure ----
namespace OAI

noncomputable section

namespace Problem310.RoutedExposure
open FiniteTableModel RoutingPath CenterRouteExposure RoutedSetDensity

/-- Translate from spatial routing with tables fixed to routing the table outcome
with the center fixed. No decision or node representation is changed. -/
theorem routedPath_eq_centerRoute {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (ω : SelectorTable b) (x : ℝ)
    (n : ℕ) (P : List (Child M)) :
    routeFrom (selectorChoice b ω) n P x = routeFrom (centerChoice b x) n P ω :=
  routeFrom_congr_at _ _ x ω (fun _ => rfl) n P

end Problem310.RoutedExposure

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutedFirstDefault ----
namespace OAI

noncomputable section

namespace Problem310.FiniteTableModel

/-- The same exact law stated with the step-by-step absence of a default.
This form pairs directly with first-default decomposition of the exposure atoms. -/
theorem outcomeLaw_no_default_steps {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    (ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1)
      {ω : SelectorTable bS × TerminalTable bT |
        ∀ k < d,
          OrderedRouting.chooseChild (fun i => selectorValue bS ω.1
            (RoutingPath.routeFrom
              (fun P y => OrderedRouting.chooseChild (fun i => selectorValue bS ω.1 P i y))
              k [] x) i x) ≠ Fin.last M} =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  convert outcomeLaw_routed_no_default bS bT p hp0 hp1 x using 1
  congr 1
  ext ω
  exact RoutingPath.noDefault_iff_not_mem
    (fun P y => OrderedRouting.chooseChild (fun i => selectorValue bS ω.1 P i y)) (Fin.last M) d x

end Problem310.FiniteTableModel

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.CenterNoDefaultMass ----
namespace OAI

noncomputable section

namespace Problem310.CenterFailureBound

open Set MeasureTheory FiniteTableModel CenterRouteExposure RoutedSetDensity

/-- The atom-averaging bad event and the spatial router's no-default event
are identical, including their terminal-table coordinate. -/
theorem noDefaultEvent_eq_spatial {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ) (x : ℝ) :
    noDefaultEvent bS bT x =
      {ω : SelectorTable bS × TerminalTable bT | ∀ k < d,
        selectorChoice bS ω.1
          (RoutingPath.routeFrom (selectorChoice bS ω.1) k [] x) x ≠ Fin.last M} := by
  ext ω
  simp only [noDefaultEvent, Set.mem_ofPred_eq,
    RoutedExposure.routedPath_eq_centerRoute,
    RoutedExposure.selectorChoice_eq_centerChoice]

/-- Exact mass of the bad event in the concrete center-atom averaging theorem.
No probability or independence premises remain. -/
theorem outcomeLaw_noDefaultEvent {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1
      (noDefaultEvent bS bT x) = (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  rw [noDefaultEvent_eq_spatial]
  exact outcomeLaw_no_default_steps bS bT p hp0 hp1 x

/-- Concrete raw-failure assembly: only the numeric depth budget and the
per-good-atom local-trial estimate are required. -/
theorem raw_failure_le_of_outcome_center_atoms {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (B : SelectorTable bS × TerminalTable bT → Set ℝ) (N : Set ℕ) (x : ℝ)
    (htail : (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d ≤ ENNReal.ofReal p)
    (hatom : ∀ ξ : Node M d × Fin M → Bool, GoodExposure bS x ξ →
      ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1
        ({ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} ∩
          centerAtom bS bT x ξ) ≤
        ENNReal.ofReal p *
          ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1
            (centerAtom bS bT x ξ)) :
    ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1
      {ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} ≤
      ENNReal.ofReal (2 * p) := by
  apply raw_failure_le_of_center_atoms bS bT
    (ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1)
    p hp0 B N x _ hatom
  rw [outcomeLaw_noDefaultEvent]
  exact htail

end Problem310.CenterFailureBound

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutingBudget ----
namespace OAI

noncomputable section

namespace Problem310.RoutingBudget

/-- The real survival estimate has exactly the expected truncated-subtraction
form for the product probability measure. -/
lemma ennreal_survival_lt {p : ℝ} (hp : 0 < p) (M d : ℕ)
    (h : (1 - ((2 : ℝ)⁻¹) ^ M) ^ d < p) :
    (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d < ENNReal.ofReal p := by
  have hbase0 : 0 ≤ 1 - ((2 : ℝ)⁻¹) ^ M := by
    have hpow : ((2 : ℝ)⁻¹) ^ M ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hbase : ENNReal.ofReal (1 - ((2 : ℝ)⁻¹) ^ M) =
      1 - ((2 : ENNReal)⁻¹) ^ M := by
    rw [ENNReal.ofReal_sub 1 (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have he := (ENNReal.ofReal_lt_ofReal_iff hp).2 h
  rwa [ENNReal.ofReal_pow hbase0, hbase] at he

end Problem310.RoutingBudget

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.Main ----
namespace OAI

noncomputable section

namespace Problem310

theorem periodic_hitting_set :
    ∀ p : ℝ, 0 < p → p < 1 → ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧ periodDensity H ≤ ENNReal.ofReal (6 * p) ∧ ∀ x t : ℝ, t ∈ Set.Icc (1 : ℝ) 2 → ∃ n : ℕ, 1 ≤ n ∧ x + t * dyadicPoint n ∈ H := by
  intro p hp hp1
  obtain ⟨M, d, R, hM, hd, hR, _, hsurvival, hbudget⟩ :=
    RoutingBudget.exists_nondefault_parameters p hp hp1
  obtain ⟨g, hg, hgeo⟩ := exists_windowData_selector_stability M d p hp
  let W := WindowConstruction.windowData (M + 1) d g R (by omega) hR
  obtain ⟨G, hG, hGp, hbad, hstable⟩ := hgeo R W
  apply Construction.periodic_hitting_of_window_failure W p hp hp1 G hG hbad
  intro x hx
  apply CenterFailureBound.raw_failure_le_of_outcome_center_atoms
    (FiniteTableModel.selectorEndpoints W) (FiniteTableModel.terminalEndpoints W)
    p hp.le hp1.le
    (RoutedSetDensity.routedSet (FiniteTableModel.selectorEndpoints W)
      (FiniteTableModel.terminalEndpoints W)) (Set.Ici 1) x
    (RoutingBudget.ennreal_survival_lt hp M d hsurvival).le
  intro ξ hξ
  apply ConcreteWindowAtom.raw_failure_on_good_atom W hM p hp.le hp1.le
    (fun r hr N hN => (hbudget r hr N hN).le) x ?_ ξ hξ
  intro P i n hn t ht ω
  exact (hstable x hx P i n hn t ht ω).symm

theorem dyadic_affine_avoidance :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasureTheory.volume E > ENNReal.ofReal (1 - η) ∧ ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x + s * dyadicPoint n ∉ E := by
  exact Problem310Support.avoidance_of_periodic_hitting periodic_hitting_set

end Problem310

end

end OAI

-- ---- mission target ----
open OAI OAI.Problem310

namespace OAI
namespace Problem310
theorem _root_.solution :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧
      MeasureTheory.volume E > ENNReal.ofReal (1 - η) ∧
      ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧
        x + s * dyadicPoint n ∉ E := by
  first
    | exact OAI.Problem310.dyadic_affine_avoidance
    | (apply OAI.Problem310.dyadic_affine_avoidance <;> assumption)
    | (intros; apply OAI.Problem310.dyadic_affine_avoidance <;> assumption)
end Problem310
end OAI
