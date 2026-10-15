-- Prove2me | solution 1 for OAI.QAC.list_disjoint_hits_length
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:04:42.068256+00:00
-- url     : https://prove2.me/submissions/9ed1dc9d-95fd-4798-9930-c6a3c8a54d92

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Transition.lean:L91-L112
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.list_disjoint_hits_length. The node keeps its source
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

lemma list_disjoint_hits_length {ι κ : Type*} [DecidableEq κ]
    (f : ι → Finset κ) (l : List ι) (hl : l.Pairwise (fun a b => Disjoint (f a) (f b)))
    (S : Finset κ) (hS : ∀ a ∈ l, (f a ∩ S).Nonempty) : l.length ≤ S.card := by
  induction l generalizing S with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.pairwise_cons.mp hl
    obtain ⟨i,hi⟩ := hS a (List.mem_cons_self ..)
    obtain ⟨hia,hiS⟩ := Finset.mem_inter.mp hi
    have hh : ∀ b ∈ l, (f b ∩ S.erase i).Nonempty := by
      intro b hb
      obtain ⟨j,hj⟩ := hS b (List.mem_cons_of_mem _ hb)
      obtain ⟨hjb,hjS⟩ := Finset.mem_inter.mp hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact Finset.disjoint_left.mp (ha b hb) hia hjb
      exact ⟨j,Finset.mem_inter.mpr ⟨hjb,Finset.mem_erase.mpr ⟨hji,hjS⟩⟩⟩
    have h := ih hl (S.erase i) hh
    simp only [List.length_cons]
    have hc := Finset.card_erase_add_one hiS
    omega

section ThreeFactors
variable {A : Type*} [CStarAlgebra A]

end ThreeFactors

section Conjugation
variable {A : Type*} [CStarAlgebra A]

end Conjugation

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem solution {ι κ : Type*} [DecidableEq κ]
    (f : ι → Finset κ) (l : List ι) (hl : l.Pairwise (fun a b => Disjoint (f a) (f b)))
    (S : Finset κ) (hS : ∀ a ∈ l, (f a ∩ S).Nonempty) : l.length ≤ S.card := by
  first
    | exact OAI.QAC.list_disjoint_hits_length f l hl S hS
    | exact OAI.QAC.list_disjoint_hits_length
    | (apply OAI.QAC.list_disjoint_hits_length <;> assumption)
    | (intros; apply OAI.QAC.list_disjoint_hits_length <;> assumption)
