-- Prove2me | solution 1 for OAI.ParityWL.inconsistent_weightedWitness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:09:56.222648+00:00
-- url     : https://prove2.me/submissions/894b0232-1eca-4a05-94b8-cfbae81aaf3f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/WeightedDual.lean:L165-L180
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.inconsistent_weightedWitness. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Theorems.Thm_OAI_ParityWL_binary_alternative
import Theorems.Thm_OAI_ParityWL_liftEquations_iff

-- ---- from OAI.Combinatorics.ParityLifts.WeightedDual ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

namespace ParityWL

open scoped BigOperators

section WeightedDual

open scoped Classical

lemma linearFunctional_expansion {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bit) →ₗ[Bit] Bit) (v : I → Bit) :
    f v = ∑ i, f (Pi.single i 1) * v i := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h : Pi.single i (v i) = v i • Pi.single i (1 : Bit) := by
    rw [← Pi.single_smul]
    simp
  rw [h, map_smul]
  exact mul_comm _ _

variable {A V W : Type} [Fintype A] [Fintype V] [Fintype W]
variable (T : SimpleGraph A) (G : SimpleGraph V) (F : SimpleGraph W)
variable (τ : G →g T) (φ : F →g G)

omit [Fintype W] in
lemma dualEdge_symm (f : (EquationRow F → Bit) →ₗ[Bit] Bit) (x y : W) :
    dualEdge F f x y = dualEdge F f y x := by
  by_cases h : F.Adj x y
  · simp [dualEdge, h, h.symm, add_comm]
  · have h' : ¬ F.Adj y x := fun hy => h hy.symm
    simp [dualEdge, h, h']

omit [Fintype W] in
lemma dualEdge_support (f : (EquationRow F → Bit) →ₗ[Bit] Bit) (x y : W)
    (h : ¬ F.Adj x y) : dualEdge F f x y = 0 := by
  simp [dualEdge, h]

omit [Fintype V] in
lemma dual_constraint_expansion (f : (EquationRow F → Bit) →ₗ[Bit] Bit)
    (z : Variables T G F τ φ) :
    f (constraintMap T G F τ φ z) =
      (∑ x, dualVertex F f x * ∑ v, z x v) +
      ∑ x, ∑ y : F.neighborSet x,
        dualEdge F f x y * z x ⟨τ (φ y), τ.map_adj (φ.map_adj y.2)⟩ := by
  rw [linearFunctional_expansion, Fintype.sum_sum_type]
  congr 1
  simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk]
  change (∑ d : F.Dart, dualDart F f d *
    (z d.fst ⟨τ (φ d.snd), τ.map_adj (φ.map_adj d.adj)⟩ + z d.snd ⟨τ (φ d.fst), τ.map_adj (φ.map_adj d.adj.symm)⟩)) = _
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hs : (∑ d : F.Dart, dualDart F f d * z d.snd ⟨τ (φ d.fst), τ.map_adj (φ.map_adj d.adj.symm)⟩) =
      ∑ d : F.Dart, dualDart F f d.symm * z d.fst ⟨τ (φ d.snd), τ.map_adj (φ.map_adj d.adj)⟩ := by
    exact (Equiv.sum_comp (dartReverseEquiv F)
      (fun d : F.Dart => dualDart F f d * z d.snd ⟨τ (φ d.fst), τ.map_adj (φ.map_adj d.adj.symm)⟩)).symm
  rw [hs, ← Finset.sum_add_distrib]
  simp_rw [← add_mul]
  calc
    _ = ∑ d : ((x : W) × F.neighborSet x),
        dualEdge F f d.1 d.2 * z d.1 ⟨τ (φ d.2), τ.map_adj (φ.map_adj d.2.2)⟩ := by
      apply Fintype.sum_equiv (dartNeighborsEquiv F)
      intro d
      dsimp [dartNeighborsEquiv]
      rw [dualEdge, dite_eq_left d.adj]
      rfl
    _ = _ := Fintype.sum_sigma _

lemma sum_subtype_indicator {I : Type} [Fintype I] {R : Type} [AddCommMonoid R]
    (p : I → Prop) [DecidablePred p] [Fintype {x // p x}] (v : I → R) :
    (∑ x : {x // p x}, v x) = ∑ x, if p x then v x else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp), Finset.sum_filter]

omit [Fintype V] [Fintype W] in
lemma variableUnit_sum (x y : W) (u : T.neighborSet (τ (φ x))) :
    (∑ v, variableUnit T G F τ φ x u y v) = if y = x then 1 else 0 := by
  by_cases h : y = x
  · subst y
    have he : ∀ v : T.neighborSet (τ (φ x)), v.1 = u.1 ↔ v = u :=
      fun _ => Subtype.ext_iff.symm
    simp [variableUnit, he]
  · simp [variableUnit, h]

omit [Fintype V] in
lemma dual_coordinate (f : (EquationRow F → Bit) →ₗ[Bit] Bit)
    (hf : ∀ z, f (constraintMap T G F τ φ z) = 0)
    (x : W) (u : T.neighborSet (τ (φ x))) :
    (∑ y, if τ (φ y) = u.1 then dualEdge F f x y else 0) = dualVertex F f x := by
  have h := hf (variableUnit T G F τ φ x u)
  rw [dual_constraint_expansion] at h
  have hv : (∑ y, dualVertex F f y *
      ∑ v, variableUnit T G F τ φ x u y v) = dualVertex F f x := by
    simp_rw [variableUnit_sum, mul_ite, mul_one, mul_zero]
    simp
  have he : (∑ v, ∑ y : F.neighborSet v, dualEdge F f v y *
      variableUnit T G F τ φ x u v ⟨τ (φ y), τ.map_adj (φ.map_adj y.2)⟩) =
      ∑ y, if τ (φ y) = u.1 then dualEdge F f x y else 0 := by
    rw [Finset.sum_eq_single x]
    · simp only [variableUnit, true_and, mul_ite, mul_one, mul_zero]
      change (∑ y : {y // F.Adj x y},
        if τ (φ y.1) = u.1 then dualEdge F f x y.1 else 0) = _
      rw [sum_subtype_indicator (F.Adj x)
        (fun y => if τ (φ y) = u.1 then dualEdge F f x y else 0)]
      apply Finset.sum_congr rfl
      intro y _
      by_cases ha : F.Adj x y
      · simp [ha]
      · simp [ha, dualEdge_support F f x y ha]
    · intro v _ hv
      simp [variableUnit, hv]
    · simp
  rw [hv, he] at h
  have h' : dualVertex F f x =
      (∑ y, if τ (φ y) = u.1 then dualEdge F f x y else 0) := by
    rwa [← CharTwo.sub_eq_add, sub_eq_zero] at h
  exact h'.symm

omit [Fintype A] [Fintype V] in
lemma dual_rhs (f : (EquationRow F → Bit) →ₗ[Bit] Bit) (b : A → Bit) :
    f (constraintRHS T G F τ φ b) = ∑ x, dualVertex F f x * b (τ (φ x)) := by
  rw [linearFunctional_expansion, Fintype.sum_sum_type]
  simp [constraintRHS, dualVertex]

omit [Fintype V] in
 theorem inconsistent_weightedWitness (b : A → Bit)
    (h : ¬ Nonempty (Solutions T G F τ φ b)) :
    Nonempty (WeightedWitness T F (τ.comp φ) b) := by
  have hn : ¬ ∃ z, constraintMap T G F τ φ z = constraintRHS T G F τ φ b := by
    rintro ⟨z, hz⟩
    exact h ⟨⟨z, (liftEquations_iff T G F τ φ b z).mpr hz⟩⟩
  obtain ⟨f, hf, hb⟩ := (binary_alternative _ _).mp hn
  refine ⟨{
    vertex := dualVertex F f
    edge := dualEdge F f
    symmetric := dualEdge_symm F f
    supported := dualEdge_support F f
    coordinate := dual_coordinate T G F τ φ f hf
    odd := ?_ }⟩
  rwa [dual_rhs] at hb

end WeightedDual

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.inconsistent_weightedWitness := @_root_.OAI.ParityWL.inconsistent_weightedWitness
