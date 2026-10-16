-- Prove2me | solution 1 for OAI.Problem310.Construction.periodic_hitting_of_window_failure
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:59:38.594193+00:00
-- url     : https://prove2.me/submissions/5251f55d-557b-4c42-9239-4a04c6c4e30d

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/Construction.lean:L15-L47
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.Construction.periodic_hitting_of_window_failure. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
import Theorems.Thm_OAI_Problem310_Auxiliary_expected_density_eq_pointwise_probability
import Theorems.Thm_OAI_Problem310_Auxiliary_periodic_hitting_of_raw_construction
import Theorems.Thm_OAI_Problem310_RandomSetDensity_pointwise_probability_selectedSet

-- ---- from OAI.MeasureTheory.DyadicAvoidance.FiniteTableModel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem310.FiniteTableModel

lemma measurable_dyadicKey (b : ℕ) : Measurable (GridSeparation.dyadicKey b) := by
  apply measurable_to_countable
  intro y
  have hm : Measurable (GridSeparation.periodicKey ((2 : ℝ) ^ (b + 2))) := by
    exact (measurable_const.mul measurable_fract).floor
  convert (measurableSet_singleton (GridSeparation.periodicKey ((2 : ℝ) ^ (b + 2)) y)).preimage hm using 1
  ext x
  exact GridSeparation.dyadicKey_eq_iff b x y

lemma measurable_selectorAddress {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (P : Node M d) (i : Fin M) : Measurable (selectorAddress b P i) := by
  exact (measurable_of_finite (fun k => (⟨(P, i), k⟩ : SelectorAddress b))).comp
    (measurable_dyadicKey (b P i))

lemma measurable_terminalAddress {M d : ℕ} (b : Leaf M d → ℕ)
    (L : Leaf M d) : Measurable (terminalAddress b L) := by
  exact (measurable_of_finite (fun k => (⟨L, k⟩ : TerminalAddress b))).comp
    (measurable_dyadicKey (b L))

lemma measurable_selectorValue {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) (i : Fin M) :
    Measurable (selectorValue b ω P i) := by
  change Measurable (fun x : ℝ => if h : P.length < d then
    ω (selectorAddress b ⟨P, h⟩ i x) else false)
  by_cases h : P.length < d
  · simp only [dite_eq_left h]
    exact (measurable_of_finite ω).comp (measurable_selectorAddress b ⟨P, h⟩ i)
  · simpa only [dite_eq_right h] using (measurable_const : Measurable (fun _ : ℝ => false))

end Problem310.FiniteTableModel

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutingPath ----
namespace OAI

universe u_ι u_X

noncomputable section

namespace Problem310.RoutingPath

variable {ι : Type u_ι} {X : Type u_X}

/-- Measurability of the finite router over a countable discrete child alphabet.
The joint node-choice map is the only input required from the table model. -/
theorem measurable_routeFrom [Countable ι]
    [MeasurableSpace X] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace (List ι)] [MeasurableSingletonClass (List ι)]
    (choose : List ι → X → ι)
    (hchoose : Measurable (Function.uncurry choose)) (n : ℕ) (P : List ι) :
    Measurable (routeFrom choose n P) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hnext : Measurable (fun x => choose (routeFrom choose n P x) x) :=
        hchoose.comp (ih.prodMk measurable_id)
      exact (measurable_of_countable (fun z : List ι × ι => z.1 ++ [z.2])).comp
        (ih.prodMk hnext)

end Problem310.RoutingPath

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RandomSetDensity ----
namespace OAI

universe u_A u_K

noncomputable section

open MeasureTheory

namespace Problem310.RandomSetDensity

/-- Finite terminal tables preserve spatial measurability of the address map. -/
theorem measurableSet_selectedSet
    {A : Type u_A} {K : Type u_K} [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (addr : A → ℝ → K) (haddr : ∀ a, Measurable (addr a))
    (z : A × (K → Bool)) : MeasurableSet (selectedSet addr z) := by
  exact ((measurable_of_countable z.2).comp (haddr z.1)) (measurableSet_singleton true)

/-- Periodicity of terminal addresses gives periodicity of every realization. -/
theorem periodic_selectedSet
    {A : Type u_A} {K : Type u_K} (addr : A → ℝ → K)
    (haddr : ∀ a x, addr a (x + 1) = addr a x) (z : A × (K → Bool)) :
    ∀ x : ℝ, x + 1 ∈ selectedSet addr z ↔ x ∈ selectedSet addr z := by
  intro x
  simp only [selectedSet, Set.mem_ofPred_eq, haddr]

/-- Exact first-moment density identity for the random routed set. -/
theorem expected_density_selectedSet
    {A : Type u_A} {K : Type u_K} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (P : Measure A) [IsProbabilityMeasure P]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (addr : A → ℝ → K) (haddr : ∀ a, Measurable (addr a)) :
    (∫⁻ z, volume (selectedSet addr z ∩ Set.Icc (0 : ℝ) 1)
      ∂(P.prod (Measure.pi (fun _ : K => ν)))) = ν {true} := by
  classical
  rw [Problem310.Auxiliary.expected_density_eq_pointwise_probability
    (P.prod (Measure.pi (fun _ : K => ν))) (selectedSet addr)
    (measurableSet_selectedSet addr haddr)]
  simp only [pointwise_probability_selectedSet P ν addr]
  simp

end Problem310.RandomSetDensity

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutedSetDensity ----
namespace OAI

noncomputable section

open MeasureTheory

namespace Problem310.RoutedSetDensity

open FiniteTableModel

lemma measurable_selectorChoice {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) : Measurable (selectorChoice b ω P) := by
  classical
  exact (measurable_of_finite (OrderedRouting.chooseChild (M := M))).comp
    (measurable_pi_iff.mpr fun i => measurable_selectorValue b ω P i)

lemma measurable_routedLeaf {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) : Measurable (routedLeaf b ω) := by
  let : MeasurableSpace (List (Child M)) := ⊤
  let : DiscreteMeasurableSpace (List (Child M)) := ⟨fun _ => trivial⟩
  have hchoose : Measurable (Function.uncurry (selectorChoice b ω)) :=
    measurable_from_prod_countable_right (measurable_selectorChoice b ω)
  have hroute := RoutingPath.measurable_routeFrom (selectorChoice b ω) hchoose d []
  apply measurable_to_countable
  intro y
  convert (measurableSet_singleton
    (RoutingPath.routeFrom (selectorChoice b ω) d [] y)).preimage hroute using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, routedLeaf]
  exact List.Vector.toList_injective.eq_iff.symm

lemma measurable_routedAddress {M d : ℕ} (bS : Node M d → Fin M → ℕ)
    (bT : Leaf M d → ℕ) (ω : SelectorTable bS) : Measurable (routedAddress bS bT ω) := by
  have hterminal : Measurable (fun z : Leaf M d × ℝ => terminalAddress bT z.1 z.2) :=
    measurable_from_prod_countable_right (measurable_terminalAddress bT)
  exact hterminal.comp ((measurable_routedLeaf bS ω).prodMk measurable_id)

lemma routedSet_periodic {M d : ℕ} (bS : Node M d → Fin M → ℕ)
    (bT : Leaf M d → ℕ) (ω : SelectorTable bS × TerminalTable bT) (x : ℝ) :
    x + 1 ∈ routedSet bS bT ω ↔ x ∈ routedSet bS bT ω :=
  RandomSetDensity.periodic_selectedSet _ (routedAddress_add_one bS bT) ω x

/-- Exact density of the concrete raw routed blocker, with no spatial regularity hypotheses. -/
theorem expected_routedSet_density {M d : ℕ} (bS : Node M d → Fin M → ℕ)
    (bT : Leaf M d → ℕ) (P : Measure (SelectorTable bS)) [IsProbabilityMeasure P]
    (ν : Measure Bool) [IsProbabilityMeasure ν] :
    (∫⁻ ω, volume (routedSet bS bT ω ∩ Set.Icc (0 : ℝ) 1)
      ∂(P.prod (Measure.pi (fun _ : TerminalAddress bT => ν)))) = ν {true} := by
  classical
  exact RandomSetDensity.expected_density_selectedSet P ν _ (measurable_routedAddress bS bT)

end Problem310.RoutedSetDensity

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.Construction ----
namespace OAI

noncomputable section

namespace Problem310.Construction

open Set MeasureTheory FiniteTableModel

/-- The analytic conclusion for the actual finite window-table model. All
regularity and first-moment obligations are discharged here; only the geometric
good-center set and its raw failure estimate remain as inputs. -/
theorem periodic_hitting_of_window_failure
    {M d g r₀ : ℕ} (W : WindowData (M + 1) d g r₀)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (G : Set ℝ) (hG : MeasurableSet G)
    (hbad : volume (Gᶜ ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p)
    (hgood : ∀ x ∈ G,
      ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
        (TerminalAddress (terminalEndpoints W)) p hp.le hp1.le
        {ω | x ∈ Auxiliary.exceptionalCenters
          (RoutedSetDensity.routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
          (Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n)} ≤ ENNReal.ofReal (2 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  classical
  apply Auxiliary.periodic_hitting_of_raw_construction
    (ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
      (TerminalAddress (terminalEndpoints W)) p hp.le hp1.le)
    p hp (RoutedSetDensity.routedSet (selectorEndpoints W) (terminalEndpoints W))
    (RoutedSetDensity.routedSet_periodic _ _) (Ici 1) (fun _ hn => hn)
    G hG hbad
  · have hmean := RoutedSetDensity.expected_routedSet_density
      (selectorEndpoints W) (terminalEndpoints W)
      (ConcreteLabels.selectorLaw (SelectorAddress (selectorEndpoints W)))
      (ConcreteLabels.bitLaw p hp.le hp1.le)
    simpa only [ConcreteLabels.outcomeLaw, ConcreteLabels.terminalLaw,
      ConcreteLabels.bitLaw_true] using hmean.le
  · exact hgood

end Problem310.Construction

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.Construction
open Set MeasureTheory FiniteTableModel


theorem solution : type_of% @_root_.OAI.Problem310.Construction.periodic_hitting_of_window_failure := @_root_.OAI.Problem310.Construction.periodic_hitting_of_window_failure
