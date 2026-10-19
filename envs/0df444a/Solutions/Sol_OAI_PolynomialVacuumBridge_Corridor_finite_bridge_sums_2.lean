-- Prove2me | solution 2 for OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:45:58.210372+00:00
-- url     : https://prove2.me/submissions/876df064-e535-4284-a022-2e6218624bf6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/BridgeFiniteness.lean:L91-L97
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_finite_bridge_sums) verbatim and is proved by it.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PolygonGeometry
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionCancellation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Traversals
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ReturnCycles
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionStems
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionGrouping
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Convexity
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_FaceBoundary
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryCharge
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryContainment
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryArcs
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexDomains
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_VisitRecursion
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryFlux
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexCuts
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RaySeparation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_StripDecay
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Reflection
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_LateralMass
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_StripWindows
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_SpatialDecay
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_LateralLength
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Bridges
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_boundary_source_weight_bound
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_lateralLengthMass_exp
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_vertexWindow_convex

-- ---- from OAI.Combinatorics.HoneycombCorridor.ConvexCuts ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem bottomSource_outside_of_strip (h : ℕ) (D : Finset Vertex)
    (hstrip : ∀ v ∈ D, InStrip h v) : (reverseGerm bottomSource).1 ∉ D := by
  intro hv
  have hh := (hstrip _ hv).1
  norm_num [bottomSource,reverseGerm,neighbor,boxIndex] at hh

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.StripWindows ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem mem_vertexWindow (h M : ℕ) (v : Vertex) : v ∈ vertexWindow h M ↔
    -(M : ℤ) ≤ boxIndex v 1 ∧ boxIndex v 1 ≤ M ∧ InStrip h v := by
  cases v <;>
    simp [vertexWindow,Finset.mem_biUnion,Finset.mem_Icc,
      Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton,InStrip,boxIndex,
      Vertex.up.injEq,Vertex.down.injEq] <;> aesop

theorem bottomSource_mem_window (h M : ℕ) (hh : 1 ≤ h) :
    bottomSource.1 ∈ vertexWindow h M := by
  rw [mem_vertexWindow]
  simp only [bottomSource,boxIndex,Fin.reduceEq,ite_false,ite_true,InStrip]
  omega

theorem vertexWindow_strip (h M : ℕ) : ∀ v ∈ vertexWindow h M, InStrip h v := by
  intro v hv
  exact ((mem_vertexWindow _ _ _).mp hv).2.2

theorem finite_vertices_in_window (h : ℕ) (S : Finset Vertex)
    (hs : ∀ v ∈ S, InStrip h v) : ∃ M : ℕ, S ⊆ vertexWindow h M := by
  let M := S.sup (fun v => (boxIndex v 1).natAbs)
  refine ⟨M,?_⟩
  intro v hv
  have ha : (boxIndex v 1).natAbs ≤ M := Finset.le_sup (f := fun v => (boxIndex v 1).natAbs) hv
  have ha' : (|(boxIndex v 1)| : ℤ) ≤ (M : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast ha
  have hab := abs_le.mp ha'
  exact (mem_vertexWindow _ _ _).mpr ⟨hab.1,hab.2,hs v hv⟩

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.Bridges ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem bridgeWord_terminal_layer (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) :
    layer (terminalGerm bottomSource (bridgeWord h hh p)).1 = (h : ℤ) :=
  (bridge_exists_word h hh p).choose_spec.2

theorem bridgeWord_injective (h : ℕ) (hh : 1 ≤ h) : Function.Injective (bridgeWord h hh) := by
  intro p q hpq
  have hv := congrArg (traced bottomSource) hpq
  simp only [bridgeWord_trace] at hv
  cases p; cases q
  cases hv
  rfl

theorem bridgeWord_mem_sourceExits (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h)
    (D : Finset Vertex) (hstrip : ∀ v ∈ D, InStrip h v)
    (hp : ∀ v ∈ p.vertices, v ∈ D) : bridgeWord h hh p ∈ sourceExits D bottomSource := by
  have ht : (terminalGerm bottomSource (bridgeWord h hh p)).1 ∉ D := by
    intro hm
    have hhi := (hstrip _ hm).2
    rw [← layer_boxIndex,bridgeWord_terminal_layer] at hhi
    omega
  apply (mem_sourceExits _ _ _).mpr
  refine ⟨stopped_of_trace D bottomSource _ ?_ ?_ ht,ht⟩
  · simpa only [bridgeWord_trace] using p.distinct
  · simpa only [bridgeWord_trace] using hp

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.BridgeFiniteness ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem finite_bridges_window (h : ℕ) (S : Finset (BridgePath h)) :
    ∃ M : ℕ, ∀ p ∈ S, ∀ v ∈ p.vertices, v ∈ vertexWindow h M := by
  classical
  let V := S.biUnion (fun p => p.vertices.toFinset)
  have hV : ∀ v ∈ V, InStrip h v := by
    intro v hv
    obtain ⟨p,hp,hv⟩ := Finset.mem_biUnion.mp hv
    have hi := p.inStrip v (List.mem_toFinset.mp hv)
    simpa only [InStrip,layer_boxIndex] using hi
  obtain ⟨M,hM⟩ := finite_vertices_in_window h V hV
  refine ⟨M,?_⟩
  intro p hp v hv
  exact hM (Finset.mem_biUnion.mpr ⟨p,hp,List.mem_toFinset.mpr hv⟩)

theorem bridge_finite_sum_word_bound (h : ℕ) (hh : 1 ≤ h) (S : Finset (BridgePath h))
    (f : List Bool → ℝ) (hf : ∀ w, 0 ≤ f w) :
    ∃ M : ℕ, (∑ p ∈ S, f (bridgeWord h hh p)) ≤
      ∑ w ∈ sourceExits (vertexWindow h M) bottomSource, f w := by
  classical
  obtain ⟨M,hM⟩ := finite_bridges_window h S
  refine ⟨M,?_⟩
  rw [← Finset.sum_image (fun p _ q _ he => bridgeWord_injective h hh he)]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun w _ _ => hf w)
  intro w hw
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hw
  exact bridgeWord_mem_sourceExits h hh p _ (vertexWindow_strip h M) (hM p hp)

theorem bridge_weight_finite_sum_bound (h : ℕ) (hh : 1 ≤ h) (S : Finset (BridgePath h)) :
    (∑ p ∈ S, weight p) ≤ (Real.cos (3*Real.pi/8))⁻¹ := by
  obtain ⟨M,hM⟩ := bridge_finite_sum_word_bound h hh S (fun w => criticalActivity^w.length)
    (fun w => pow_nonneg criticalActivity_pos.le _)
  simp only [bridgeWord_length] at hM
  apply hM.trans
  exact boundary_source_weight_bound _ bottomSource (vertexWindow_convex h M)
    (bottomSource_mem_window h M hh)
    (bottomSource_outside_of_strip h _ (vertexWindow_strip h M))

theorem sourceExit_reaches_zero (D : Finset Vertex) (hg : bottomSource.1 ∈ D)
    (w : List Bool) (hw : w ∈ sourceExits D bottomSource) : reachesDistance 0 w := by
  cases w with
  | nil =>
    have hn := ((mem_sourceExits _ _ _).mp hw).1
    exact False.elim (hn hg)
  | cons b w => exact ⟨bottomSource.1,by simp [traced],abs_nonneg _⟩

theorem lateralLengthMass_zero (D : Finset Vertex) (hg : bottomSource.1 ∈ D) :
    lateralLengthMass D 0 = ∑ w ∈ sourceExits D bottomSource,
      (w.length : ℝ)*criticalActivity^w.length := by
  classical
  unfold lateralLengthMass
  apply Finset.sum_congr rfl
  intro w hw
  simp only [sourceExit_reaches_zero D hg w hw,ite_true]

theorem bridge_length_finite_sum_bound (h : ℕ) (hh : 1 ≤ h) (S : Finset (BridgePath h)) :
    (∑ p ∈ S, firstLengthWeight p) ≤ tailConstant*spatialConstant*((h : ℝ)+1)^2 := by
  obtain ⟨M,hM⟩ := bridge_finite_sum_word_bound h hh S
    (fun w => (w.length : ℝ)*criticalActivity^w.length)
    (fun w => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg criticalActivity_pos.le _))
  simp only [bridgeWord_length] at hM
  rw [← lateralLengthMass_zero _ (bottomSource_mem_window h M hh)] at hM
  apply hM.trans
  have ht := lateralLengthMass_exp h hh _ (vertexWindow_convex h M)
    (bottomSource_mem_window h M hh) (vertexWindow_strip h M) 0 le_rfl
  simpa only [mul_zero,zero_div,Real.exp_zero,mul_one] using ht

theorem bridge_weight_summable (h : ℕ) (hh : 1 ≤ h) : Summable (weight (h := h)) := by
  refine summable_of_sum_le (f := weight (h := h))
    (c := (Real.cos (3*Real.pi/8))⁻¹) ?_ (bridge_weight_finite_sum_bound h hh)
  intro p
  exact pow_nonneg criticalActivity_pos.le p.vertices.length

theorem bridge_length_summable (h : ℕ) (hh : 1 ≤ h) : Summable (firstLengthWeight (h := h)) := by
  refine summable_of_sum_le (f := firstLengthWeight (h := h))
    (c := tailConstant*spatialConstant*((h : ℝ)+1)^2) ?_
    (bridge_length_finite_sum_bound h hh)
  intro p
  exact mul_nonneg (Nat.cast_nonneg p.vertices.length)
    (pow_nonneg criticalActivity_pos.le p.vertices.length)

theorem finite_bridge_sums : FiniteBridgeSums := by
  intro h hh
  have hm := bridge_weight_summable h hh
  have hl := bridge_length_summable h hh
  have hmc : Summable (fun p : ConfinedBridgePath h => weight p.val) := hm.subtype InLogCorridor
  have hlc : Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) := hl.subtype InLogCorridor
  exact ⟨hm,hl,hl.div_const _,hmc,hlc,hlc.div_const _⟩

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- mission target ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

namespace OAI
namespace PolynomialVacuumBridge.Corridor
theorem _root_.solution : FiniteBridgeSums := by
  first
    | exact OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums
    | (apply OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums <;> assumption)
    | (intros; apply OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums <;> assumption)
end PolynomialVacuumBridge.Corridor
end OAI
