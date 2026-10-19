-- Prove2me | solution 1 for OAI.AdaptiveReveals.Scheme.badMass_eq_probability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:06:06.23399+00:00
-- url     : https://prove2.me/submissions/e2db1826-2dc6-498e-ac5d-8f3321e5abd8

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse
import Definitions.Def_OAI_Probability_CriticalZ3_AdaptiveReveals

open OAI OAI.AdaptiveReveals OAI.AdaptiveReveals.Scheme
universe uF
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical
open InfiniteConditioning
variable {E V S : Type} [Countable E] [DecidableEq V]
variable (P : Scheme E V S)


omit [DecidableEq V] in
theorem solution (s : S) : P.badMass s =
    (ProductCylinder.law (P.parameter s)).real
      {ω | P.bad s ((P.reveal s).restrict ω) = true} := by
  classical
  set J := P.reveal s
  set μ := ProductCylinder.law (P.parameter s)
  have hpat : ∀ a : J → Bool, pattern J (ProductCylinder.extend J a) = (fun ω : E → Bool => J.restrict ω) ⁻¹' {a} := by
    intro a
    ext ω
    simp only [pattern, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, ProductCylinder.extend]
    constructor
    · intro h; funext e; have := h e.1 e.2; simpa [e.2] using this
    · intro h e he; rw [← h]; simp [he]
  have hset : {ω | P.bad s (J.restrict ω) = true} =
      (fun ω : E → Bool => J.restrict ω) ⁻¹' ((Finset.univ.filter (fun a : J → Bool => P.bad s a = true) : Finset _) : Set (J → Bool)) := by
    ext ω; simp
  unfold badMass weight
  rw [hset, ← sum_measureReal_preimage_singleton _ (fun y _ =>
    (Finset.measurable_restrict (X := fun _ : E => Bool) J) (measurableSet_singleton y)), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hpat]

