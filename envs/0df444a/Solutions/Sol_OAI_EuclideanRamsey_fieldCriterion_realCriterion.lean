-- Prove2me | solution 1 for OAI.EuclideanRamsey.fieldCriterion_realCriterion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:50:34.113479+00:00
-- url     : https://prove2.me/submissions/f8ab8d1e-c4f1-4320-80a9-0fe6f31856a0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/TensorDescent.lean:L147-L172
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.fieldCriterion_realCriterion. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent

-- ---- from OAI.Combinatorics.EuclideanRamsey.TensorDescent ----
-- Backport the two-case eliminator from Mathlib/LinearAlgebra/TensorProduct/Defs.lean
-- at d13f23b723b8a846827a245b89c10fc7d3f11612, using the 4.33.1 eliminator.
section Lean433TensorProductCompatibility
open scoped TensorProduct
variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
namespace TensorProduct
@[elab_as_elim, induction_eliminator]
private theorem inductionOn {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z
    (by simpa only [TensorProduct.zero_tmul] using tmul (0 : M) (0 : N)) tmul add
end TensorProduct
end Lean433TensorProductCompatibility

namespace OAI

universe uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

section Descent
variable (F : IntermediateField ℚ ℝ) {ι : Type uIndex} (b : Module.Basis ι F ℝ)

variable (φ : ℝ →ₗ[F] F)

attribute [local instance] OAI.EuclideanRamsey.tensorRing
end Descent

end EuclideanRamsey

namespace EuclideanRamsey
open scoped TensorProduct BigOperators

theorem fieldCriterion_realCriterion {s d : ℕ} (a : Fin s → Space d)
    (h : FieldCriterion a) : RealCriterion a := by
  classical
  obtain ⟨P,hP,hG⟩ := h
  let φ : TensorRing a →ₐ[ℚ] RealTensor :=
    Algebra.TensorProduct.map (coordinateField a).val (coordinateField a).val
  have haug (i : Fin s) (α : Option (Fin d)) :
      ((augmented a i α : Coeff a) : ℝ) = realAugmented a i α := by
    cases α <;> rfl
  have hmul (T : TensorRing a) :
      Algebra.TensorProduct.lmul' ℚ (φ T) = (multiply a T : ℝ) := by
    induction T using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp [hx,hy]
  refine ⟨fun α β => φ (P α β),?_,?_⟩
  · intro i
    have hh := congrArg φ (hP i)
    have hφ (x y : Coeff a) : φ (x ⊗ₜ[ℚ] y) = (x:ℝ) ⊗ₜ[ℚ] (y:ℝ) := rfl
    change (∑ α,∑ β,(realAugmented a i α ⊗ₜ[ℚ] (1:ℝ))*φ (P α β)*
      ((1:ℝ) ⊗ₜ[ℚ] realAugmented a i β)) = 0
    simpa only [map_sum,map_mul,map_zero,hφ,haug,OneMemClass.coe_one] using hh
  · ext α β
    change Algebra.TensorProduct.lmul' ℚ (φ (P (some α) (some β))) = _
    rw [hmul,hG]
    simp only [Matrix.one_apply]
    split_ifs <;> rfl

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped TensorProduct BigOperators


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.fieldCriterion_realCriterion := @_root_.OAI.EuclideanRamsey.fieldCriterion_realCriterion
