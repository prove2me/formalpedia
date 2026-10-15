-- Prove2me | solution 1 for OAI.QAC.weight_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:13:08.857705+00:00
-- url     : https://prove2.me/submissions/0e85ac1a-ff6d-4a55-9998-0a8ed2865b88

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Polynomial.lean:L57-L74
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.weight_mul_le. The node keeps its source
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

-- ---- from OAI.InformationTheory.QuantumCircuit.Polynomial ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

namespace QAC

lemma weight_add_le {R : ℝ} (hR : 0 ≤ R) (p q : ℝ[X]) :
    weight R (p + q) ≤ weight R p + weight R q := by
  let s := p.support ∪ q.support
  have hf : ∀ i : ℕ, |(0 : ℝ)| * R ^ i = 0 := by simp
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  unfold weight
  rw [sum_eq_of_subset _ hf (support_add.trans (Finset.Subset.refl s)),
    sum_eq_of_subset _ hf hp, sum_eq_of_subset _ hf hq, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    rw [coeff_add, ← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (pow_nonneg hR _)

lemma weight_sum_le {ι : Type*} {R : ℝ} (hR : 0 ≤ R) (s : Finset ι) (p : ι → ℝ[X]) :
    weight R (∑ i ∈ s, p i) ≤ ∑ i ∈ s, weight R (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (weight_add_le hR (p i) (∑ j ∈ s, p j)).trans (add_le_add_right ih _)

lemma weight_mul_le {R : ℝ} (hR : 0 ≤ R) (p q : ℝ[X]) :
    weight R (p * q) ≤ weight R p * weight R q := by
  rw [mul_eq_sum_sum]
  apply (weight_sum_le hR _ _).trans
  calc
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support,
        weight R (monomial (i + j) (p.coeff i * q.coeff j)) :=
      Finset.sum_le_sum fun i _ => weight_sum_le hR _ _
    _ = weight R p * weight R q := by
      simp_rw [weight_monomial, abs_mul, pow_add]
      unfold weight Polynomial.sum
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

theorem solution {R : ℝ} (hR : 0 ≤ R) (p q : ℝ[X]) :
    weight R (p * q) ≤ weight R p * weight R q := by
  first
    | exact OAI.QAC.weight_mul_le hR p q
    | exact OAI.QAC.weight_mul_le
    | (apply OAI.QAC.weight_mul_le <;> assumption)
    | (intros; apply OAI.QAC.weight_mul_le <;> assumption)
