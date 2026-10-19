-- Prove2me | solution 1 for OAI.CriticalZ3.LatticeGraph.bondMeets_probability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:06:52.958987+00:00
-- url     : https://prove2.me/submissions/2305083f-51e6-447e-bf55-86086f5e8c52

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph

open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical MeasureTheory ProbabilityTheory
variable (G : LatticeGraph)
theorem cz_bondConn_iff (G : LatticeGraph) (ω : BondConfig) (x y : G.Node) :
    G.BondConn ω x y ↔ HyperedgeComparison.Connected G.hypergraph
      (fun e => ω e.1) ∅ x y := by
  unfold LatticeGraph.BondConn HyperedgeComparison.Connected
  constructor
  · intro h
    refine Relation.ReflTransGen.mono (fun a b hab => ?_) _ _ h
    obtain ⟨e, he, hinc, hω⟩ := hab
    refine ⟨⟨e, he⟩, hω, Set.disjoint_empty _, ?_, ?_⟩ <;>
      rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> first | exact Or.inl h1 | exact Or.inr h1 | exact Or.inl h2 | exact Or.inr h2
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b _ hab ih =>
      obtain ⟨⟨e, he⟩, hω, -, ha, hb⟩ := hab
      by_cases hab' : a = b
      · subst hab'; exact ih
      · refine ih.tail ⟨e, he, ?_, hω⟩
        change a.1 = e.1 ∨ a.1 = step e.1 e.2 at ha
        change b.1 = e.1 ∨ b.1 = step e.1 e.2 at hb
        have hne : a.1 ≠ b.1 := fun h => hab' (Subtype.ext h)
        unfold Incidence
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact absurd (ha.trans hb.symm) hne
        · exact Or.inl ⟨ha, hb⟩
        · exact Or.inr ⟨hb, ha⟩
        · exact absurd (ha.trans hb.symm) hne

theorem cz_obs (G : LatticeGraph) (p : Bond → Set.Icc (0 : ℝ) 1)
    (φ : (G.Node → Set Vertex → Prop) → Prop) :
    (ProductCylinder.law p).real {ω | φ (G.BondMeets ω)} =
      HyperedgeComparison.eventProb (fun e : G.edges => p e.1)
        (fun ω => φ (fun o T => HyperedgeComparison.Meets G.hypergraph ω ∅ o {y | y.1 ∈ T})) := by
  classical
  set S : Set (G.edges → Bool) :=
    {ξ | φ (fun o T => HyperedgeComparison.Meets G.hypergraph ξ ∅ o {y | y.1 ∈ T})} with hS
  have hSm : MeasurableSet S := S.toFinite.measurableSet
  have hpre : {ω : BondConfig | φ (G.BondMeets ω)} = (Finset.restrict G.edges) ⁻¹' S := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hS]
    have : G.BondMeets ω = (fun o T => HyperedgeComparison.Meets G.hypergraph
        (Finset.restrict G.edges ω) ∅ o {y | y.1 ∈ T}) := by
      funext o T
      apply propext
      unfold LatticeGraph.BondMeets HyperedgeComparison.Meets
      constructor
      · rintro ⟨y, hy, hc⟩; exact ⟨y, hy, (cz_bondConn_iff G ω o y).mp hc⟩
      · rintro ⟨y, hy, hc⟩; exact ⟨y, hy, (cz_bondConn_iff G ω o y).mpr hc⟩
    rw [this]
  rw [hpre, ← map_measureReal_apply (Finset.measurable_restrict _) hSm]
  unfold ProductCylinder.law
  rw [Measure.infinitePi_map_restrict]
  unfold HyperedgeComparison.eventProb
  have : (fun ω : G.edges → Bool => if (φ (fun o T => HyperedgeComparison.Meets G.hypergraph ω ∅ o {y | y.1 ∈ T})) then (1:ℝ) else 0)
      = S.indicator 1 := by
    funext ω; simp [Set.indicator, hS]
  rw [this, integral_indicator_one hSm]
  rfl

theorem solution (p : Bond → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (T : Set Vertex) :
    (ProductCylinder.law p).real {ω | G.BondMeets ω o T} =
      HyperedgeComparison.eventProb (fun e : G.edges => p e.1)
        (fun ω => HyperedgeComparison.Meets G.hypergraph ω ∅ o {y | y.1 ∈ T}) := by
  exact cz_obs G p (fun M => M o T)

