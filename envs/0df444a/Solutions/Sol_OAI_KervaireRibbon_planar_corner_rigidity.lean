-- Prove2me | solution 1 for OAI.KervaireRibbon.planar_corner_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:59:39.476314+00:00
-- url     : https://prove2.me/submissions/0a97e16d-4eff-4f96-9dae-90d0ae7ba9d3

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/RibbonRigidity.lean:L181-L241
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.planar_corner_rigidity. The node keeps its source
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
import Theorems.Thm_OAI_KervaireBoundary_planar_boundary
import Theorems.Thm_OAI_KervaireRibbon_exists_cycle_coordinates
import Theorems.Thm_OAI_KervaireRibbon_one_defect_of_holonomy
import Theorems.Thm_OAI_KervaireRibbon_reachable_of_component

-- ---- from OAI.GroupTheory.Kervaire.ComponentFibers ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

end

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

omit [Fintype D] [DecidableEq D] in
lemma numCycles_eq_card_of_projection {V : Type*} [Fintype D] [Fintype V]
    (σ : Perm D) (f : D → V) (hf : Function.Surjective f)
    (hs : ∀ x y, σ.SameCycle x y ↔ f x = f y) : numCycles σ = Fintype.card V := by
  have he : SameCycle.setoid σ = Setoid.ker f := Setoid.ext hs
  unfold numCycles Cycles
  exact (Fintype.card_congr (Quotient.congrRight (Setoid.ext_iff.mp he))).trans
    (Fintype.card_congr (Setoid.quotientKerEquivOfSurjective f hf))

end

open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

end KervaireRibbon

end

end OAI

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

lemma holonomy_of_coboundary [Fintype D] (σ : Equiv.Perm D) (b u : D → A)
    {Z : Type*} (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D)
    (he : ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (z : Z) (hu : ∀ i, b (e ⟨z,i⟩) = u (σ (e ⟨z,i⟩)) * (u (e ⟨z,i⟩))⁻¹) :
    orbitWeight (finRotate (n z+1)) (fun i ↦ b (e ⟨z,i⟩)) (n z+1) 0 = 1 := by
  have hf : (fun i ↦ b (e ⟨z,i⟩)) = (fun i ↦ u (e ⟨z,finRotate _ i⟩) * (u (e ⟨z,i⟩))⁻¹) := by
    funext i
    rw [hu,he]
  rw [hf]
  have hh := orbitWeight_coboundary (finRotate (n z+1)) (fun i ↦ u (e ⟨z,i⟩)) (n z+1) 0
  rw [rotate_pow_self] at hh
  simpa using hh
end

open Equiv Equiv.Perm KervaireCycle KervaireMixing KervaireTraversal KervaireBoundary
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

omit [Fintype I] [Fintype K] in
lemma successor_pow_inl (ρ : Perm I) (k : K) (i : I) (n : ℕ) :
    ((successor (K := K) ρ)^n) (Sum.inl k,i) = (Sum.inl k,(ρ^n) i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',mul_apply,ih,pow_succ']; rfl

omit [Fintype I] [Fintype K] in
lemma successor_pow_inr (ρ : Perm I) (k : K) (i : I) (n : ℕ) :
    ((successor (K := K) ρ)^n) (Sum.inr k,i) = (Sum.inr k,(ρ.symm^n) i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',mul_apply,ih,pow_succ']; rfl

lemma successor_cycles (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (x y : Slot I K) :
    (successor ρ).SameCycle x y ↔ x.1 = y.1 := by
  constructor
  · intro h
    exact sameCycle_map_eq (successor ρ) Prod.fst (by rintro ⟨k|k,i⟩ <;> rfl) h
  · rcases x with ⟨k,i⟩
    rcases y with ⟨l,j⟩
    intro h
    dsimp at h
    subst l
    cases k with
    | inl k =>
      obtain ⟨n,hn⟩ := (hρ i j).exists_nat_pow_eq
      have hh : ((successor (K := K) ρ)^n) (Sum.inl k,i) = (Sum.inl k,j) := by
        rw [successor_pow_inl,hn]
      exact hh ▸ SameCycle.rfl.pow_right
    | inr k =>
      obtain ⟨n,hn⟩ := (hρ i j).inv.exists_nat_pow_eq
      have hh : ((successor (K := K) ρ)^n) (Sum.inr k,i) = (Sum.inr k,j) := by
        rw [successor_pow_inr]
        exact congrArg (fun q ↦ (Sum.inr k,q)) hn
      exact hh ▸ SameCycle.rfl.pow_right

lemma numCycles_successor [Nonempty I] (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) :
    numCycles (successor (K := K) ρ) = 2*Fintype.card K := by
  have hh := numCycles_eq_card_of_projection (successor (K := K) ρ) Prod.fst
    (fun k ↦ ⟨(k,Classical.arbitrary I),rfl⟩) (successor_cycles ρ hρ)
  simpa only [Fintype.card_sum,two_mul] using hh

omit [Fintype I] [Fintype K] in
lemma traversal_ne_zero (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (d : Slot I K) :
    traversalSign s d ≠ 0 := by
  rcases d with ⟨k|k,i⟩ <;> rcases hs i with h | h <;> simp [traversalSign,h]

/-- A single deviating corner on a connected planar assembly of literal word
 disks cannot carry a nontrivial defect. This is the analytic boundary theorem,
 with all other circuit products discharged by gauge telescoping. -/
theorem planar_corner_rigidity [Nonempty I] [Nonempty K]
    (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (θ : Perm (Slot I K)) (hθ : ∀ d, θ (θ d) = d)
    (hop : ∀ d, traversalSign s (θ d) = - traversalSign s d)
    (hconn : components (successor ρ) θ = ⊤) (hp : planar (successor ρ) θ)
    (u : Slot I K → A) (p : Slot I K)
    (hu : ∀ d, d ≠ p → (labels ρ a d)⁻¹ = u (θ d) * (u (successor ρ d))⁻¹) :
    (labels ρ a p)⁻¹ = u (θ p) * (u (successor ρ p))⁻¹ := by
  let σ := successor (K := K) ρ
  let φ := σ*θ
  obtain ⟨n,e,he⟩ := exists_cycle_coordinates φ
  let z₀ : Cycles φ := (e.symm (θ p)).1
  have hc : ∀ z, z ≠ z₀ → orbitWeight (finRotate (n z+1))
      (fun i ↦ labels ρ a (θ (e ⟨z,i⟩))) (n z+1) 0 = 1 := by
    intro z hz
    apply holonomy_of_coboundary φ (fun d ↦ labels ρ a (θ d)) u n e he z
    intro i
    have hne : θ (e ⟨z,i⟩) ≠ p := by
      intro hh
      have hh' : e ⟨z,i⟩ = θ p := by simpa only [hθ] using congrArg θ hh
      have hh'' := congrArg (fun d ↦ (e.symm d).1) hh'
      exact hz (by simpa only [e.symm_apply_apply] using hh'')
    have hh := congrArg Inv.inv (hu _ hne)
    simpa only [φ,σ,Equiv.Perm.mul_apply,inv_inv,_root_.mul_inv_rev,hθ] using hh
  have htne (d : Slot I K) : θ d ≠ d := by
    intro hd
    have hh := hop d
    rw [hd] at hh
    have hn := traversal_ne_zero s hs d
    omega
  have ht := numCycles_involution θ hθ htne
  have hv := numCycles_successor (K := K) ρ hρ
  have hall := hp
  unfold planar at hall
  rw [hconn,classes_top,hv] at hall
  have hcard : Fintype.card (Slot I K) = 2*(Fintype.card I*Fintype.card K) := by
    simp only [Slot,Fintype.card_prod,Fintype.card_sum]
    ring
  rw [hcard] at ht hall
  have hEuler : Fintype.card (Cycles φ) + 2*Fintype.card K = 2+Fintype.card I*Fintype.card K := by
    change numCycles φ + _ = _
    dsimp [φ,σ] at *
    omega
  have hb := KervaireBoundary.planar_boundary ρ a s hs hsum θ hθ hop n e he
    (fun d f ↦ reachable_of_component σ θ (x := d) (y := f) (by rw [hconn]; trivial)) hEuler z₀ hc
  have hm (z : Cycles φ) : orbitWeight (finRotate (n z+1))
      (fun i ↦ labels ρ a (θ (e ⟨z,i⟩))) (n z+1) 0 = 1 := by
    by_cases hz : z = z₀
    · subst z; exact hb
    · exact hc z hz
  have hh := one_defect_of_holonomy φ (fun d ↦ labels ρ a (θ d)) u (θ p) n e he (by
    intro d hd
    have hdp : θ d ≠ p := fun h ↦ hd (by simpa only [hθ] using congrArg θ h)
    have hh := congrArg Inv.inv (hu (θ d) hdp)
    simpa only [φ,σ,Equiv.Perm.mul_apply,inv_inv,_root_.mul_inv_rev,hθ] using hh) hm
  have hi := congrArg Inv.inv hh
  simpa only [φ,σ,Equiv.Perm.mul_apply,hθ,_root_.mul_inv_rev,inv_inv] using hi
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
open Equiv Equiv.Perm KervaireCycle KervaireMixing KervaireTraversal KervaireBoundary
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.planar_corner_rigidity := @_root_.OAI.KervaireRibbon.planar_corner_rigidity
