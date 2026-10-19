-- Prove2me | solution 1 for OAI.KervaireRibbon.relator_corner_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:07:05.636463+00:00
-- url     : https://prove2.me/submissions/896cdcef-2e4e-4406-bf14-bd49ad118d71

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/RelatorRigidity.lean:L271-L348
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.relator_corner_rigidity. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Kervaire_RelatorRigidity
import Theorems.Thm_OAI_KervaireRibbon_balanced_vertices
import Theorems.Thm_OAI_KervaireRibbon_planar_corner_rigidity

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

omit [DecidableEq D] in
lemma numCycles_equiv {B : Type*} [Fintype B] (e : D ≃ B) (σ : Perm D) :
    numCycles (e.symm.trans (σ.trans e)) = numCycles σ := by
  symm
  apply Fintype.card_congr
  exact Quotient.congr e (fun x y ↦ by
    change (∃ n : ℤ, (σ^n) x = y) ↔ ∃ n : ℤ, ((e.permCongrHom σ)^n) (e x) = e y
    apply exists_congr
    intro n
    rw [← map_zpow]
    change (σ^n) x = y ↔ e ((σ^n) (e.symm (e x))) = e y
    rw [e.symm_apply_apply,e.injective.eq_iff])
end

open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

end KervaireRibbon

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.RelatorRigidity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

end

section
open Equiv Equiv.Perm
open scoped Classical
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

lemma components_equiv (e : D ≃ B) (σ θ : Perm D) (x y : D) :
    components (e.permCongrHom σ) (e.permCongrHom θ) (e x) (e y) ↔ components σ θ x y := by
  constructor
  · intro h
    have hh := components_map e.symm _ _ σ θ (by intro d; simp [Equiv.permCongrHom])
      (by intro d; simp [Equiv.permCongrHom]) h
    simpa only [e.symm_apply_apply] using hh
  · exact components_map e σ θ _ _ (fun d ↦ by simp [Equiv.permCongrHom])
      (fun d ↦ by simp [Equiv.permCongrHom])

lemma classes_components_equiv (e : D ≃ B) (σ θ : Perm D) :
    classes (components (e.permCongrHom σ) (e.permCongrHom θ)) = classes (components σ θ) := by
  symm
  exact Fintype.card_congr (Quotient.congr e (fun x y ↦ (components_equiv e σ θ x y).symm))

lemma planar_equiv (e : D ≃ B) (σ θ : Perm D) :
    planar (e.permCongrHom σ) (e.permCongrHom θ) ↔ planar σ θ := by
  unfold planar
  rw [← map_mul]
  have hnum (τ : Perm D) : numCycles (e.permCongrHom τ) = numCycles τ := numCycles_equiv e τ
  rw [hnum σ,hnum θ,hnum (σ*θ),classes_components_equiv]
  rw [Fintype.card_congr e]

lemma connected_equiv (e : D ≃ B) (σ θ : Perm D) (hc : components σ θ = ⊤) :
    components (e.permCongrHom σ) (e.permCongrHom θ) = ⊤ := by
  apply top_unique
  intro x y _
  obtain ⟨x,rfl⟩ := e.surjective x
  obtain ⟨y,rfl⟩ := e.surjective y
  apply (components_equiv e σ θ x y).mpr
  rw [hc]
  trivial
end

section
open Equiv Equiv.Perm
open scoped Classical
variable {V I D : Type*} [Fintype V] [Fintype I] [Fintype D]

lemma sum_eq_zero_of_opposite (θ : Perm D) (t : D → ℤ) (ht : ∀ d, t (θ d) = -t d) : ∑ d, t d = 0 := by
  have hh := Equiv.sum_comp θ t
  rw [Finset.sum_congr rfl (fun d _ ↦ ht d),Finset.sum_neg_distrib] at hh
  omega

lemma vertex_balance (e : V × I ≃ D) (ε : V → ℤ) (s : I → ℤ)
    (hs : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1) (θ : Perm D) (t : D → ℤ)
    (ht : ∀ d, t (θ d) = -t d) (he : ∀ v i, t (e (v,i)) = ε v*s i) :
    ∑ v, ε v = 0 := by
  have hh := sum_eq_zero_of_opposite θ t ht
  rw [← e.sum_comp] at hh
  have hm : (∑ vi : V × I, t (e vi)) = (∑ v, ε v) * (∑ i, s i) := by
    simp only [Fintype.sum_prod_type,he,← Finset.mul_sum,← Finset.sum_mul]
  rw [hm] at hh
  rcases hs with hs | hs <;> rw [hs] at hh <;> simpa using hh

end

open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

theorem relator_corner_rigidity [Nonempty I]
    (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (e : V × I ≃ D) (ε : V → ℤ) (hε : ∀ v, ε v = 1 ∨ ε v = -1)
    (σ θ : Perm D) (hσ : ∀ v i, σ (e (v,i)) = e (vertexNext ρ ε (v,i)))
    (hθ : ∀ d, θ (θ d) = d) (t : D → ℤ)
    (ht : ∀ d, t (θ d) = -t d) (he : ∀ v i, t (e (v,i)) = ε v*s i)
    (hconn : components σ θ = ⊤) (hp : planar σ θ)
    (u : D → A) (p : D)
    (hu : ∀ v i, e (v,i) ≠ p → vertexCorner ρ a ε (v,i) = corner σ θ u (e (v,i))) :
    vertexCorner ρ a ε (e.symm p) = corner σ θ u p := by
  have hz := vertex_balance e ε s hsum θ t ht he
  obtain ⟨q,hqP,hqN⟩ := balanced_vertices ε hε hz
  let K := {v // ε v = 1}
  have hK : Nonempty K := by
    have hV : Nonempty V := ⟨(e.symm p).1⟩
    let v := Classical.arbitrary V
    rcases q.symm v with k | k
    · exact ⟨k⟩
    · exact ⟨k⟩
  let E : KervaireMixing.Slot I K ≃ D := (Equiv.prodCongr q (Equiv.refl I)).trans e
  let S := KervaireMixing.successor (K := K) ρ
  let T := E.symm.permCongrHom θ
  have hES : ∀ d, σ (E d) = E (S d) := by
    rintro ⟨k|k,i⟩
    · change σ (e (q (Sum.inl k),i)) = e (q (Sum.inl k),ρ i)
      simpa only [vertexNext,hqP,ite_true] using hσ (q (Sum.inl k)) i
    · change σ (e (q (Sum.inr k),i)) = e (q (Sum.inr k),ρ.symm i)
      simpa only [vertexNext,hqN,show (-1:ℤ) ≠ 1 by omega,ite_false] using hσ (q (Sum.inr k)) i
  have hS : E.symm.permCongrHom σ = S := by
    apply Equiv.ext
    intro d
    change E.symm (σ (E d)) = _
    rw [hES,E.symm_apply_apply]
  have hT (d) : T (T d) = d := by
    change E.symm (θ (E (E.symm (θ (E d))))) = d
    rw [E.apply_symm_apply,hθ,E.symm_apply_apply]
  have htE (d) : t (E d) = KervaireBoundary.traversalSign s d := by
    rcases d with ⟨k|k,i⟩
    · change t (e (q (Sum.inl k),i)) = s i
      rw [he,hqP,one_mul]
    · change t (e (q (Sum.inr k),i)) = -s i
      rw [he,hqN,neg_one_mul]
  have hop (d) : KervaireBoundary.traversalSign s (T d) = - KervaireBoundary.traversalSign s d := by
    rw [← htE,← htE]
    change t (E (E.symm (θ (E d)))) = _
    rw [E.apply_symm_apply,ht]
  have hconn' : components S T = ⊤ := by
    rw [← hS]
    exact connected_equiv E.symm σ θ hconn
  have hp' : planar S T := by
    rw [← hS]
    exact (planar_equiv E.symm σ θ).mpr hp
  have hl (d) : (KervaireMixing.labels ρ a d)⁻¹ =
      vertexCorner ρ a ε (e.symm (E d)) := by
    rcases d with ⟨k|k,i⟩
    · change (a i)⁻¹⁻¹ = vertexCorner ρ a ε (e.symm (e (q (Sum.inl k),i)))
      simp only [e.symm_apply_apply,vertexCorner,hqP,ite_true,inv_inv]
    · change (a (ρ.symm i))⁻¹ = vertexCorner ρ a ε (e.symm (e (q (Sum.inr k),i)))
      simp only [e.symm_apply_apply,vertexCorner,hqN,show (-1:ℤ) ≠ 1 by omega,ite_false]
  have hc (d) : corner S T (u ∘ E) d = corner σ θ u (E d) := by
    simp only [corner,Function.comp_apply]
    change u (E (E.symm (θ (E d)))) * _ = _
    rw [E.apply_symm_apply,← hES]
  have hh := planar_corner_rigidity ρ hρ a s hs hsum T hT hop hconn' hp'
    (u ∘ E) (E.symm p) (by
      intro d hd
      rw [hl]
      change _ = corner S T (u ∘ E) d
      rw [hc]
      have hne : E d ≠ p := fun h ↦ hd (E.injective (h.trans (E.apply_symm_apply p).symm))
      simpa only [Prod.mk.eta,e.apply_symm_apply] using
        hu (e.symm (E d)).1 (e.symm (E d)).2 (by simpa only [Prod.mk.eta,e.apply_symm_apply] using hne))
  change _ = corner σ θ u p
  rw [hl] at hh
  change _ = corner S T (u ∘ E) (E.symm p) at hh
  rw [hc,E.apply_symm_apply] at hh
  exact hh

end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.relator_corner_rigidity := @_root_.OAI.KervaireRibbon.relator_corner_rigidity
