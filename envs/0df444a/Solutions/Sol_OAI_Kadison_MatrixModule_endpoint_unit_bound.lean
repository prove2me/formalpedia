-- Prove2me | solution 1 for OAI.Kadison.MatrixModule.endpoint_unit_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:06:02.173973+00:00
-- url     : https://prove2.me/submissions/02a45e97-aae2-43bb-82fe-5059edd8da69

import Mathlib
import Definitions.Def_OAIQ039C010
import Definitions.Def_OAIQ039C011
import Definitions.Def_OAIQ039C019

section
-- module Solutions.OAIQ039_CM.Commutator_EndpointModule
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

namespace Kadison.HilbertTensor

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

lemma inner_map_left_symmetric (a : E →L[ℂ] E)
    (ha : ∀ x y, inner ℂ (a x) y = inner ℂ x (a y))
    (x y : Completion (E ⊗[ℂ] F)) :
    inner ℂ (map a (1 : F →L[ℂ] F) x) y =
      inner ℂ x (map a (1 : F →L[ℂ] F) y) := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y =>
    induction x using OAI.tensorInductionOn with
    | add x x' hx hx' =>
      simp only [Completion.coe_add, map_add, inner_add_left, hx, hx']
    | tmul x v =>
      induction y using OAI.tensorInductionOn with
      | add y y' hy hy' =>
        simp only [Completion.coe_add, map_add, inner_add_right, hy, hy']
      | tmul y w =>
        simp only [map_coe_tmul, one_apply_eq_self, Completion.inner_coe,
          TensorProduct.inner_tmul, ha]

lemma endpoint_projection_bound
    (Y : Completion (E ⊗[ℂ] F) →L[ℂ] Completion (E ⊗[ℂ] G))
    (p : E →L[ℂ] E)
    (hp : ∀ x y, inner ℂ (p x) y = inner ℂ x (p y))
    (hY : Y.comp (map p (1 : F →L[ℂ] F)) =
      (map p (1 : G →L[ℂ] G)).comp Y)
    (Ω a : E) (ha : p a = a) (x : F) (z : G) :
    ‖inner ℂ ((a ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _)
      (Y ((Ω ⊗ₜ[ℂ] x : E ⊗[ℂ] F) : Completion _))‖ ≤
      ‖Y‖ * ‖a‖ * ‖p Ω‖ * ‖x‖ * ‖z‖ := by
  have htest : map p (1 : G →L[ℂ] G)
      ((a ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _) =
      ((a ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _) := by
    simp [ha]
  have heq : inner ℂ ((a ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _)
      (Y ((Ω ⊗ₜ[ℂ] x : E ⊗[ℂ] F) : Completion _)) =
      inner ℂ ((a ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _)
      (Y ((p Ω ⊗ₜ[ℂ] x : E ⊗[ℂ] F) : Completion _)) := by
    conv_lhs => rw [← htest]
    rw [inner_map_left_symmetric p hp, ← ContinuousLinearMap.comp_apply,
      ← hY, ContinuousLinearMap.comp_apply, map_coe_tmul, one_apply_eq_self]
  rw [heq]
  calc
    _ ≤ ‖((a ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _)‖ *
        ‖Y ((p Ω ⊗ₜ[ℂ] x : E ⊗[ℂ] F) : Completion _)‖ := norm_inner_le_norm _ _
    _ ≤ (‖a‖ * ‖z‖) * (‖Y‖ * (‖p Ω‖ * ‖x‖)) := by
      simp only [Completion.norm_coe, TensorProduct.norm_tmul]
      gcongr
      simpa only [Completion.norm_coe, TensorProduct.norm_tmul] using
        (Y.le_opNorm ((p Ω ⊗ₜ[ℂ] x : E ⊗[ℂ] F) : Completion _))
    _ = _ := by ring

end Kadison.HilbertTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EndpointModule2
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

variable {I : Type*} [Fintype I] [DecidableEq I]

namespace MatrixModule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable (ρ : Matrix I I ℂ →⋆ₐ[ℂ] (E →L[ℂ] E)) (Ω : E)
  (htrace : ∀ a, inner ℂ Ω (ρ a Ω) = normalizedTrace a)

include htrace in
lemma inner_vector (a b : Matrix I I ℂ) :
    inner ℂ (ρ a Ω) (ρ b Ω) = normalizedTrace (star a * b) := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ Ω (star (ρ a) (ρ b Ω)) = _
  rw [← map_star]
  change inner ℂ Ω ((ρ (star a) * ρ b) Ω) = _
  rw [← map_mul, htrace]

include htrace in
lemma norm_vector_single (i j : I) :
    ‖ρ (Matrix.single i j 1) Ω‖ = Real.sqrt (Fintype.card I : ℝ)⁻¹ := by
  have hs : ‖ρ (Matrix.single i j 1) Ω‖ ^ 2 = (Fintype.card I : ℝ)⁻¹ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_vector ρ Ω htrace]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single,
      star_one, Matrix.single_mul_single_same, normalizedTrace,
      Matrix.trace_single_eq_same, mul_one]
    change ((Fintype.card I : ℂ)⁻¹).re = _
    rw [Complex.inv_re]
    simp
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

lemma projection_symmetric (i : I) :
    ∀ x y : E, inner ℂ (ρ (Matrix.single i i 1) x) y =
      inner ℂ x (ρ (Matrix.single i i 1) y) := by
  intro x y
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ x (star (ρ (Matrix.single i i 1)) y) = _
  rw [← map_star]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]

lemma projection_fixes_single (i j : I) :
    ρ (Matrix.single i i 1) (ρ (Matrix.single i j 1) Ω) =
      ρ (Matrix.single i j 1) Ω := by
  change (ρ (Matrix.single i i 1) * ρ (Matrix.single i j 1)) Ω = _
  rw [← map_mul, Matrix.single_mul_single_same, one_mul]

variable {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

include htrace in
lemma endpoint_unit_bound_oai
    (Y : Completion (E ⊗[ℂ] F) →L[ℂ] Completion (E ⊗[ℂ] G))
    (hY : ∀ a, Y.comp (HilbertTensor.map (ρ a) (1 : F →L[ℂ] F)) =
      (HilbertTensor.map (ρ a) (1 : G →L[ℂ] G)).comp Y)
    (i j : I) (x : F) (z : G) :
    ‖inner ℂ ((ρ (Matrix.single i j 1) Ω ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _)
      (Y ((Ω ⊗ₜ[ℂ] x : E ⊗[ℂ] F) : Completion _))‖ ≤
      ‖Y‖ * (Fintype.card I : ℝ)⁻¹ * ‖x‖ * ‖z‖ := by
  have h := HilbertTensor.endpoint_projection_bound Y (ρ (Matrix.single i i 1))
    (projection_symmetric ρ i) (hY _) Ω (ρ (Matrix.single i j 1) Ω)
    (projection_fixes_single ρ Ω i j) x z
  rw [norm_vector_single ρ Ω htrace, norm_vector_single ρ Ω htrace,
    mul_assoc ‖Y‖, ← sq, Real.sq_sqrt (inv_nonneg.mpr (Nat.cast_nonneg _))] at h
  exact h

end MatrixModule

end Kadison
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Kadison.MatrixModule.endpoint_unit_bound_oai.{u_1, u_2, u_3, u_4} := @OAI.Kadison.MatrixModule.endpoint_unit_bound_oai.{u_1, u_2, u_3, u_4}
