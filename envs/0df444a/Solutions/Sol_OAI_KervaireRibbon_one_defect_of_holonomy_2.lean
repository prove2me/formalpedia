-- Prove2me | solution 2 for OAI.KervaireRibbon.one_defect_of_holonomy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:58:04.060388+00:00
-- url     : https://prove2.me/submissions/1a3af733-cd46-403a-9701-f297743446ff

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/RibbonRigidity.lean:L95-L113
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.one_defect_of_holonomy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow

-- ---- from OAI.GroupTheory.Kervaire.RibbonRigidity ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix

namespace KervaireRibbon

section
open Equiv Equiv.Perm KervaireCycle
open scoped Classical
variable {D A : Type*} [Group A]

lemma orbitWeight_coboundary (σ : Equiv.Perm D) (u : D → A) (n : ℕ) (d : D) :
    orbitWeight σ (fun x ↦ u (σ x) * (u x)⁻¹) n d = u ((σ^n) d) * (u d)⁻¹ := by
  induction n with
  | zero => simp [orbitWeight]
  | succ n ih =>
    rw [orbitWeight_succ,ih,pow_succ',mul_apply]
    group

lemma list_prod_single_difference {B : Type*} (l : List B) (hl : l.Nodup) (f g : B → A)
    (x : B) (hx : x ∈ l) (hfg : ∀ y ∈ l, y ≠ x → f y = g y)
    (hp : (l.map f).prod = (l.map g).prod) : f x = g x := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    obtain ⟨hy,hl⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons,List.prod_cons] at hp
    by_cases hxy : x = y
    · subst y
      have ht : l.map f = l.map g := List.map_congr_left (fun z hz ↦
        hfg z (List.mem_cons_of_mem _ hz) (fun he ↦ hy (he ▸ hz)))
      rw [ht] at hp
      exact mul_right_cancel hp
    · have hyx := Ne.symm hxy
      rw [hfg y (List.mem_cons_self ..) hyx] at hp
      exact ih hl (List.mem_of_ne_of_mem hxy hx)
        (fun z hz ↦ hfg z (List.mem_cons_of_mem _ hz)) (mul_left_cancel hp)

lemma orbitWeight_as_list (σ : Equiv.Perm D) (b : D → A) (n : ℕ) (d : D) :
    orbitWeight σ b n d = ((List.ofFn (fun i : Fin n ↦ (σ^i.val) d)).reverse.map b).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [orbitWeight_succ,ih,List.ofFn_succ',List.concat_eq_append,List.reverse_concat]
    simp only [List.map_cons,List.prod_cons]
    rfl

lemma rotate_orbit_list (n : ℕ) [NeZero n] :
    List.ofFn (fun i : Fin n ↦ ((finRotate n)^i.val) 0) = List.ofFn (fun i : Fin n ↦ i) := by
  congr 1
  funext i
  rw [rotate_pow_apply]
  simp

lemma orbitWeight_single_difference (n : ℕ) [NeZero n] (f g : Fin n → A)
    (j : Fin n) (hfg : ∀ i, i ≠ j → f i = g i)
    (hp : orbitWeight (finRotate n) f n 0 = orbitWeight (finRotate n) g n 0) : f j = g j := by
  rw [orbitWeight_as_list,orbitWeight_as_list,rotate_orbit_list] at hp
  apply list_prod_single_difference _ _ f g j _ (fun i _ ↦ hfg i) hp
  · exact List.nodup_reverse.mpr (List.nodup_ofFn.mpr Function.injective_id)
  · simp only [List.mem_reverse,List.mem_ofFn]
    exact ⟨j,rfl⟩

/-- A connection which is a pure gauge away from one directed corner is a pure
 gauge everywhere as soon as its exceptional face has trivial holonomy. -/
lemma one_defect_of_holonomy [Fintype D] (σ : Equiv.Perm D) (b u : D → A) (p : D)
    {Z : Type*} (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D)
    (he : ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (hu : ∀ d, d ≠ p → b d = u (σ d) * (u d)⁻¹)
    (hm : ∀ z, orbitWeight (finRotate (n z+1)) (fun i ↦ b (e ⟨z,i⟩)) (n z+1) 0 = 1) :
    b p = u (σ p) * (u p)⁻¹ := by
  obtain ⟨⟨z,j⟩,rfl⟩ := e.surjective p
  let v : Fin (n z+1) → A := fun i ↦ u (e ⟨z,i⟩)
  have hv := orbitWeight_coboundary (finRotate (n z+1)) v (n z+1) 0
  rw [rotate_pow_self] at hv
  simp only [one_apply,mul_inv_cancel] at hv
  have hh := orbitWeight_single_difference (n z+1) (fun i ↦ b (e ⟨z,i⟩))
    (fun i ↦ v (finRotate _ i) * (v i)⁻¹) j (by
      intro i hij
      rw [hu _ (fun h ↦ hij (eq_of_heq (Sigma.mk.inj_iff.mp (e.injective h)).2))]
      rw [he]) ((hm z).trans hv.symm)
  simpa only [v,← he] using hh

end

open Equiv Equiv.Perm KervaireCycle KervaireMixing KervaireTraversal KervaireBoundary
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix
open Equiv Equiv.Perm KervaireCycle
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.one_defect_of_holonomy := @_root_.OAI.KervaireRibbon.one_defect_of_holonomy
