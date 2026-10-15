-- Prove2me | solution 1 for OAI.QAC.ancillaProjection_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:34:01.635738+00:00
-- url     : https://prove2.me/submissions/854246e8-b38f-46b1-80d0-d95e9f54cf82

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Ancilla.lean:L66-L85
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.ancillaProjection_diagonal. The node keeps its source
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

-- ---- from OAI.InformationTheory.QuantumCircuit.Toffoli ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma rankOne_basis (b : Bit) (x y : Bit) :
    rankOne (basisVector b) x y = if x=b ∧ y=b then 1 else 0 := by
  classical
  simp only [rankOne,basisVector]
  split_ifs <;> simp_all

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Computational ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma tensorMatrix_diagonal {N : ℕ} (f : Fin N → Bit → ℂ) :
    tensorMatrix (fun i => Matrix.diagonal (f i)) = Matrix.diagonal (fun x => ∏ i, f i (x i)) := by
  classical
  ext x y
  simp only [tensorMatrix,Matrix.diagonal_apply]
  by_cases hxy : x=y
  · subst y; simp
  · simp only [ite_eq_right hxy]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma rankOne_basis_diagonal (b : Bit) :
    rankOne (basisVector b) = Matrix.diagonal (fun x => if x=b then 1 else 0) := by
  ext x y
  rw [rankOne_basis,Matrix.diagonal_apply]
  split_ifs <;> simp_all

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Ancilla ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma ancillaProjection_diagonal (n N : ℕ) :
    ancillaProjection n N = Matrix.diagonal (fun z => if ancillaValid n z then 1 else 0) := by
  classical
  have hloc : (fun i : Fin N => if i.val<n then (1 : QubitOperator) else rankOne (basisVector 0)) =
      fun i => Matrix.diagonal (fun b => if n ≤ i.val → b=0 then (1:ℂ) else 0) := by
    funext i
    by_cases hi : i.val<n
    · simp [hi,not_le.mpr hi,Matrix.diagonal_one]
    · simp [hi,not_lt.mp hi,rankOne_basis_diagonal]
  rw [ancillaProjection,hloc,tensorMatrix_diagonal]
  congr 1
  funext z
  by_cases hz : ancillaValid n z
  · rw [ite_eq_left hz]
    apply Finset.prod_eq_one
    intro i _
    exact ite_eq_left (hz i)
  · rw [ite_eq_right hz]
    obtain ⟨i,hi⟩ := not_forall.mp hz
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

theorem solution (n N : ℕ) :
    ancillaProjection n N = Matrix.diagonal (fun z => if ancillaValid n z then 1 else 0) := by
  first
    | exact OAI.QAC.ancillaProjection_diagonal n N
    | exact OAI.QAC.ancillaProjection_diagonal
    | (apply OAI.QAC.ancillaProjection_diagonal <;> assumption)
    | (intros; apply OAI.QAC.ancillaProjection_diagonal <;> assumption)
