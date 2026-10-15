-- Prove2me | solution 1 for OAI.QAC.list_conjugate_filter
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:08:32.229818+00:00
-- url     : https://prove2.me/submissions/a9633ce8-cd50-4010-ae3d-49c5438df3e3

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Transition.lean:L208-L232
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.list_conjugate_filter. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition

-- ---- from OAI.InformationTheory.QuantumCircuit.Transition ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

section NormAlgebra
variable {A : Type*} [CStarAlgebra A]

end NormAlgebra

section ThreeFactors
variable {A : Type*} [CStarAlgebra A]

end ThreeFactors

section Conjugation
variable {A : Type*} [CStarAlgebra A]

lemma conjugate_comp (U V B : A) : conjugate (U*V) B = conjugate U (conjugate V B) := by
  simp only [conjugate,star_mul,mul_assoc]

lemma conjugate_fixed {U B : A} (hU : U ∈ unitary A) (h : Commute U B) :
    conjugate U B = B := by
  rw [conjugate,h.eq,mul_assoc,Unitary.mul_star_self_of_mem hU,mul_one]

lemma list_conjugate_filter {ι : Type*} (f : ι → A) (l : List ι) (p : ι → Bool) (B : A)
    (hl : l.Pairwise (fun a b => Commute (f a) (f b)))
    (hu : ∀ a ∈ l, f a ∈ unitary A)
    (hd : ∀ a ∈ l, p a = false → Commute (f a) B) :
    conjugate (l.map f).prod B = conjugate ((l.filter p).map f).prod B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.pairwise_cons.mp hl
    have hu' : ∀ b ∈ l, f b ∈ unitary A := fun b hb => hu b (List.mem_cons_of_mem _ hb)
    have hd' : ∀ b ∈ l, p b = false → Commute (f b) B := fun b hb => hd b (List.mem_cons_of_mem _ hb)
    have hc : Commute (f a) (l.map f).prod := by
      apply Commute.list_prod_right
      intro x hx
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
      exact ha b hb
    cases hpa : p a with
    | false =>
      simp only [List.map_cons,List.prod_cons,List.filter_cons,hpa,Bool.false_eq_true,ite_false]
      rw [hc.eq,conjugate_comp,conjugate_fixed (hu a (List.mem_cons_self ..))
        (hd a (List.mem_cons_self ..) hpa)]
      exact ih hl hu' hd'
    | true =>
      simp only [List.map_cons,List.prod_cons,List.filter_cons,hpa,ite_true,List.map_cons,List.prod_cons]
      rw [conjugate_comp,conjugate_comp,ih hl hu' hd']
end Conjugation

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix
variable {A : Type*} [CStarAlgebra A]

theorem solution {ι : Type*} (f : ι → A) (l : List ι) (p : ι → Bool) (B : A)
    (hl : l.Pairwise (fun a b => Commute (f a) (f b)))
    (hu : ∀ a ∈ l, f a ∈ unitary A)
    (hd : ∀ a ∈ l, p a = false → Commute (f a) B) :
    conjugate (l.map f).prod B = conjugate ((l.filter p).map f).prod B := by
  first
    | exact OAI.QAC.list_conjugate_filter f l p B hl hu hd
    | exact OAI.QAC.list_conjugate_filter
    | (apply OAI.QAC.list_conjugate_filter <;> assumption)
    | (intros; apply OAI.QAC.list_conjugate_filter <;> assumption)
