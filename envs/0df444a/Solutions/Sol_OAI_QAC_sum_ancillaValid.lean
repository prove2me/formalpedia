-- Prove2me | solution 1 for OAI.QAC.sum_ancillaValid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:32:08.392574+00:00
-- url     : https://prove2.me/submissions/17547934-081e-491d-89b4-d965e72dd075

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Ancilla.lean:L45-L61
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.sum_ancillaValid. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Toffoli
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Physical
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Computational
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Ancilla

-- ---- from OAI.InformationTheory.QuantumCircuit.Ancilla ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma restrict_inputWord {n N : ℕ} (hnN : n ≤ N) (x : Word n) :
    restrictWord hnN (inputWord x)=x := by
  funext i
  simp [restrictWord,inputWord,i.isLt]

lemma inputWord_injective {n N : ℕ} (hnN : n ≤ N) :
    Function.Injective (@inputWord n N) :=
  Function.LeftInverse.injective (restrict_inputWord hnN)

lemma inputWord_valid {n N : ℕ} (x : Word n) : ancillaValid n (@inputWord n N x) := by
  intro i hi
  simp [inputWord,not_lt.mpr hi]

lemma input_restrictWord {n N : ℕ} (hnN : n ≤ N) (z : Word N) (hz : ancillaValid n z) :
    inputWord (restrictWord hnN z)=z := by
  funext i
  by_cases hi : i.val<n
  · simp [inputWord,hi,restrictWord]
  · simp [inputWord,hi,hz i (not_lt.mp hi)]

lemma sum_ancillaValid {n N : ℕ} (hnN : n ≤ N) {α : Type*} [AddCommMonoid α]
    (f : Word N → α) :
    (∑ z : Word N, if ancillaValid n z then f z else 0) = ∑ x : Word n, f (inputWord x) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun x _ => inputWord x)
  · intro x _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact inputWord_valid x
  · intro x _ y _ hxy
    exact inputWord_injective hnN hxy
  · intro z hz
    refine ⟨restrictWord hnN z,Finset.mem_univ _,?_⟩
    exact input_restrictWord hnN z (Finset.mem_filter.mp hz).2
  · intro x _
    rfl

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

theorem solution {n N : ℕ} (hnN : n ≤ N) {α : Type*} [AddCommMonoid α]
    (f : Word N → α) :
    (∑ z : Word N, if ancillaValid n z then f z else 0) = ∑ x : Word n, f (inputWord x) := by
  first
    | exact OAI.QAC.sum_ancillaValid hnN f
    | exact OAI.QAC.sum_ancillaValid
    | (apply OAI.QAC.sum_ancillaValid <;> assumption)
    | (intros; apply OAI.QAC.sum_ancillaValid <;> assumption)
