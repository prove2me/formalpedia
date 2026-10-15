-- Prove2me | solution 1 for OAI.QAC.parity_advantage_from_entries
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:36:58.532727+00:00
-- url     : https://prove2.me/submissions/c4936daa-4e70-434e-9dd0-6d2be764b818

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Measurement.lean:L81-L107
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.parity_advantage_from_entries. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ParityTrace
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Measurement
import Theorems.Thm_OAI_QAC_parity_trace_identity

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

-- ---- from OAI.InformationTheory.QuantumCircuit.ParityTrace ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma bitSign_add (a b : Bit) : bitSign (a+b)=bitSign a*bitSign b := by
  fin_cases a <;> fin_cases b <;> norm_num [bitSign,Fin.add_def,Fin.ext_iff]

lemma bitSign_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Bit) :
    bitSign (∑ i ∈ s, f i)=∏ i ∈ s, bitSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bitSign]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,Finset.prod_insert hi,bitSign_add,ih]

lemma bitSign_parity {n : ℕ} (x : Word n) : bitSign (parity x)=∏ i, bitSign (x i) :=
  bitSign_finset_sum _ _

lemma sum_bitSign_parity {n : ℕ} (hn : 0<n) : (∑ x : Word n, bitSign (parity x))=0 := by
  simp only [bitSign_parity]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bit) => bitSign b)]
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨0,hn⟩ : Fin n)) (by norm_num [Fin.sum_univ_two,bitSign])

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Measurement ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma outputZeroCount_diagonal {N : ℕ} (out : Fin N) :
    (outputZeroCount out).zero = Matrix.diagonal (fun z => if z out=0 then 1 else 0) := by
  classical
  have hloc : (fun i : Fin N => if i=out then rankOne (basisVector 0) else (1:QubitOperator)) =
      fun i => Matrix.diagonal (fun b => if i=out → b=0 then (1:ℂ) else 0) := by
    funext i
    by_cases hi : i=out
    · simp [hi,rankOne_basis_diagonal]
    · simp [hi,Matrix.diagonal_one]
  simp only [Count.zero,outputZeroCount,Finset.mem_singleton]
  rw [hloc,tensorMatrix_diagonal]
  congr 1
  funext z
  rw [Fintype.prod_boole]
  simp

lemma born_zero_diagonal {N : ℕ} (W : Operator N) (out : Fin N) (z : Word N) :
    (star W*(outputZeroCount out).zero*W) z z = (outputProbability W out 0 z:ℂ) := by
  classical
  rw [outputZeroCount_diagonal,Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.star_apply,outputProbability,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y out=0
  · simp only [ite_eq_left hy,mul_one,Complex.star_def,← Complex.normSq_eq_conj_mul_self]
  · simp [hy]

lemma total_born_probability {N : ℕ} (W : Operator N) (hW : W ∈ unitary (Operator N))
    (z : Word N) : (∑ y, Complex.normSq (W y z))=1 := by
  apply Complex.ofReal_injective
  have h := congrArg (fun A : Operator N => A z z) (Unitary.star_mul_self_of_mem hW)
  simpa only [Matrix.mul_apply,Matrix.star_apply,Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self,← Complex.ofReal_sum,Matrix.one_apply_eq,Complex.ofReal_one] using h

lemma outputProbability_complement {N : ℕ} (W : Operator N) (hW : W ∈ unitary (Operator N))
    (out : Fin N) (z : Word N) :
    outputProbability W out 0 z+outputProbability W out 1 z=1 := by
  rw [outputProbability,outputProbability,← Finset.sum_add_distrib,← total_born_probability W hW z]
  apply Finset.sum_congr rfl
  intro y _
  generalize y out=b
  fin_cases b <;> simp

lemma success_character_lower {n N : ℕ} (W : Operator N) (hW : W ∈ unitary (Operator N))
    (out : Fin N) (x : Word n) {ε : ℝ} (hsuccess : 1/2+ε ≤ successProbability W out x) :
    ε+bitSign (parity x)/2 ≤
      ((bitSign (parity x):ℂ)*(star W*(outputZeroCount out).zero*W) (inputWord x) (inputWord x)).re := by
  rw [born_zero_diagonal,← Complex.ofReal_mul,Complex.ofReal_re]
  have htotal := outputProbability_complement W hW out (inputWord x)
  change 1/2+ε ≤ outputProbability W out (parity x) (inputWord x) at hsuccess
  generalize hp : parity x=b at hsuccess ⊢
  fin_cases b
  · norm_num [bitSign] at *
    linarith only [hsuccess]
  · norm_num [bitSign] at *
    linarith only [hsuccess,htotal]

/-- The finite Fourier step, with all final garbage summed out by the Born rule. -/
lemma parity_advantage_from_entries {n N : ℕ} (hn : 0<n) (hnN : n ≤ N)
    (W : Operator N) (hW : W ∈ unitary (Operator N)) (out : Fin N) {ε δ : ℝ}
    (hsuccess : ∀ x : Word n, 1/2+ε ≤ successProbability W out x)
    (hentry : ∀ x : Word n,
      ‖(localMatrix (inputHadamard n N)*(star W*(outputZeroCount out).zero*W)*
        localMatrix (inputHadamard n N)) (flipWord (inputSet n N) (inputWord x)) (inputWord x)‖ ≤ δ) :
    ε ≤ δ := by
  let B := star W*(outputZeroCount out).zero*W
  let H := localMatrix (inputHadamard n N)
  have hlow := Finset.sum_le_sum (fun (x : Word n) (_ : x∈Finset.univ) =>
    success_character_lower W hW out x (hsuccess x))
  have hzero := sum_bitSign_parity hn
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ← Finset.sum_div,hzero,zero_div,add_zero] at hlow
  have hupp := Finset.sum_le_sum (fun (x : Word n) (_ : x∈Finset.univ) =>
    (Complex.re_le_norm ((H*B*H) (flipWord (inputSet n N) (inputWord x)) (inputWord x))).trans (hentry x))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hupp
  have heq := congrArg Complex.re (parity_trace_identity hnN B)
  have hsumre (f : Word n → ℂ) : (∑ x, f x).re = ∑ x, (f x).re :=
    map_sum Complex.reAddGroupHom f Finset.univ
  rw [hsumre,hsumre] at heq
  change (∑ x : Word n, ((H*B*H) (flipWord (inputSet n N) (inputWord x)) (inputWord x)).re) =
    ∑ x : Word n, ((bitSign (parity x):ℂ)*B (inputWord x) (inputWord x)).re at heq
  rw [heq] at hupp
  have hc : 0 < (Fintype.card (Word n):ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  exact (mul_le_mul_iff_right₀ hc).mp (hlow.trans hupp)

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

theorem solution {n N : ℕ} (hn : 0<n) (hnN : n ≤ N)
    (W : Operator N) (hW : W ∈ unitary (Operator N)) (out : Fin N) {ε δ : ℝ}
    (hsuccess : ∀ x : Word n, 1/2+ε ≤ successProbability W out x)
    (hentry : ∀ x : Word n,
      ‖(localMatrix (inputHadamard n N)*(star W*(outputZeroCount out).zero*W)*
        localMatrix (inputHadamard n N)) (flipWord (inputSet n N) (inputWord x)) (inputWord x)‖ ≤ δ) :
    ε ≤ δ := by
  first
    | exact OAI.QAC.parity_advantage_from_entries hn hnN W hW out hsuccess hentry
    | exact OAI.QAC.parity_advantage_from_entries
    | (apply OAI.QAC.parity_advantage_from_entries <;> assumption)
    | (intros; apply OAI.QAC.parity_advantage_from_entries <;> assumption)
