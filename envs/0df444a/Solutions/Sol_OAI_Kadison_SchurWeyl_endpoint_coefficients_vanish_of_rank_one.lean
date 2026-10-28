-- Prove2me | solution 1 for OAI.Kadison.SchurWeyl.endpoint_coefficients_vanish_of_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:32:23.175103+00:00
-- url     : https://prove2.me/submissions/a48ec1a1-b33f-43d7-87db-5d5e17e97d07

import Mathlib
import Definitions.Def_OAIQ039C029

section
-- module Solutions.OAIQ039_CM.Commutator_InvariantForms
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [DecidableEq J] in
lemma tensorMatrices_single (a b : J → I) :
    tensorMatrices (fun j => Matrix.single (a j) (b j) (1 : 𝕜)) = Matrix.single a b 1 := by
  classical
  ext c d
  simp only [tensorMatrices, Matrix.single_apply]
  by_cases h : c = a ∧ d = b
  · rcases h with ⟨rfl, rfl⟩; simp
  · rw [ite_eq_right (by simpa [eq_comm] using h)]
    have he : ∃ j, ¬ (a j = c j ∧ b j = d j) := by
      by_contra! hn
      exact h ⟨funext fun j => (hn j).1.symm, funext fun j => (hn j).2.symm⟩
    obtain ⟨j, hj⟩ := he
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CycleInvariants
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma rawCycleTrace_single (b : J → I) (hb : Function.Injective b)
    (σ τ : Equiv.Perm J) :
    rawCycleTrace σ (fun j => Matrix.single (b (τ j)) (b j) (1 : 𝕜)) =
      if σ = τ then 1 else 0 := by
  classical
  unfold rawCycleTrace
  rw [tensorMatrices_single, Matrix.trace_mul_single]
  simp only [MulOpposite.op_one, one_smul, permutationMatrix]
  have he : b = (fun j => b (τ j)) ∘ σ.symm ↔ σ = τ := by
    constructor
    · intro h
      apply Equiv.ext
      intro j
      apply hb
      simpa using congrFun h (σ j)
    · rintro rfl
      ext j
      simp
  by_cases h : σ = τ
  · subst τ
    simp [Function.comp_def]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h (he.mp hh))]

lemma cycleTrace_single (b : J → I) (hb : Function.Injective b)
    (σ τ : Equiv.Perm J) :
    cycleTrace σ (fun j => Matrix.single (b (τ j)) (b j) 1) =
      if σ = τ then (Fintype.card I : ℂ)⁻¹ ^ cycleCount τ else 0 := by
  rw [cycleTrace, rawCycleTrace_single b hb]
  split_ifs with h
  · subst τ; rw [mul_one]
  · rw [mul_zero]

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EndpointElimination
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion

namespace Kadison

theorem coefficient_zero_of_unbounded_stages
    (z : ℂ) (C : ℝ) (p c : ℕ) (m : ℕ → ℕ)
    (hm : ∀ B : ℕ, ∃ n, B ≤ m n)
    (hbound : ∀ n, ‖z‖ ^ 2 * (m n : ℝ) ^ (p + 1) ≤
      C ^ 2 * (m n : ℝ) ^ (2 * c))
    (hc : 2 * c < p + 1) : z = 0 := by
  by_contra hz
  have hl : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  obtain ⟨B, hB⟩ := exists_nat_gt (max (C ^ 2 / ‖z‖ ^ 2) 1)
  obtain ⟨n, hn⟩ := hm B
  have hmn : (B : ℝ) ≤ m n := by exact_mod_cast hn
  have hm1 : 1 < (m n : ℝ) := (lt_of_le_of_lt (le_max_right _ _) hB).trans_le hmn
  have ht : C ^ 2 / ‖z‖ ^ 2 < (m n : ℝ) :=
    (lt_of_le_of_lt (le_max_left _ _) hB).trans_le hmn
  have hh := hbound n
  have hpow : (m n : ℝ) ^ (2 * c + 1) ≤ (m n : ℝ) ^ (p + 1) :=
    pow_le_pow_right₀ hm1.le hc
  have hpowpos : 0 < (m n : ℝ) ^ (2 * c) := pow_pos (by linarith) _
  have hh' : ‖z‖ ^ 2 * (m n : ℝ) ^ (2 * c + 1) ≤
      C ^ 2 * (m n : ℝ) ^ (2 * c) :=
    (mul_le_mul_of_nonneg_left hpow hl.le).trans hh
  rw [pow_succ (m n : ℝ) (2 * c)] at hh'
  have hle : ‖z‖ ^ 2 * (m n : ℝ) ≤ C ^ 2 := by
    apply (mul_le_mul_iff_right₀ hpowpos).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh'
  have hgt : C ^ 2 < (m n : ℝ) * ‖z‖ ^ 2 := (div_lt_iff₀ hl).mp ht
  nlinarith

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EndpointElimination3
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison

theorem square_endpoint_unit_bound (r C m : ℝ) (p c : ℕ)
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hm : 0 < m) (hp : 1 ≤ p)
    (h : r * (m⁻¹) ^ c ≤ C * m⁻¹ * (Real.sqrt m⁻¹) ^ (p - 1)) :
    r ^ 2 * m ^ (p + 1) ≤ C ^ 2 * m ^ (2 * c) := by
  have hq : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
  have hleft : (r * (m⁻¹) ^ c) ^ 2 = r ^ 2 * (m⁻¹) ^ (2 * c) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm c 2]
  have hright : (C * m⁻¹ * (Real.sqrt m⁻¹) ^ (p - 1)) ^ 2 =
      C ^ 2 * (m⁻¹) ^ (p + 1) := by
    simp only [mul_pow]
    rw [pow_right_comm (Real.sqrt m⁻¹) (p - 1) 2, Real.sq_sqrt hq,
      mul_assoc, ← pow_add, show 2 + (p - 1) = p + 1 by omega]
  have hs := (sq_le_sq₀ (mul_nonneg hr (pow_nonneg hq _))
    (mul_nonneg (mul_nonneg hC hq) (pow_nonneg (Real.sqrt_nonneg _) _))).mpr h
  rw [hleft, hright, inv_pow, inv_pow, ← div_eq_mul_inv, ← div_eq_mul_inv] at hs
  exact (div_le_div_iff₀ (pow_pos hm _) (pow_pos hm _)).mp hs

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EndpointRankOne
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.SchurWeyl

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem endpoint_coefficients_vanish_of_rank_one_oai
    (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
    (a : J) (b : ∀ n, J → I n) (hb : ∀ n, Function.Injective (b n))
    (F : ∀ n, (J → Matrix (I n) (I n) ℂ) → ℂ)
    (c : Equiv.Perm J → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n A, F n A = ∑ σ, c σ * cycleTrace σ A)
    (hbound : ∀ n (σ : Equiv.Perm J), ‖F n (fun j => Matrix.single (b n (σ j)) (b n j) 1)‖ ≤
      C * (Fintype.card (I n) : ℝ)⁻¹ *
        (Real.sqrt (Fintype.card (I n) : ℝ)⁻¹) ^ (Fintype.card J - 1))
    (hunbounded : ∀ B : ℕ, ∃ n, B ≤ Fintype.card (I n))
    (σ : Equiv.Perm J) (hσ : 2 * cycleCount σ < Fintype.card J + 1) : c σ = 0 := by
  refine coefficient_zero_of_unbounded_stages
    (c σ) C (Fintype.card J) (cycleCount σ) (fun n => Fintype.card (I n))
    hunbounded ?_ hσ
  intro n
  have hI : 0 < (Fintype.card (I n) : ℝ) := by
    have : Nonempty (I n) := ⟨b n a⟩
    exact_mod_cast Fintype.card_pos
  have hp : 1 ≤ Fintype.card J := by
    have : Nonempty J := ⟨a⟩
    exact Fintype.card_pos
  apply square_endpoint_unit_bound ‖c σ‖ C (Fintype.card (I n)) (Fintype.card J)
    (cycleCount σ) (norm_nonneg _) hC hI hp
  have he : F n (fun j => Matrix.single (b n (σ j)) (b n j) 1) =
      c σ * ((Fintype.card (I n) : ℂ)⁻¹) ^ cycleCount σ := by
    rw [hF]
    simp only [cycleTrace_single (b n) (hb n), mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hh := hbound n σ
  simpa only [he, norm_mul, norm_pow, norm_inv, Complex.norm_natCast] using hh

end Kadison.SchurWeyl
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.SchurWeyl.endpoint_coefficients_vanish_of_rank_one_oai.{u_1, u_2} := @OAI.Kadison.SchurWeyl.endpoint_coefficients_vanish_of_rank_one_oai.{u_1, u_2}
