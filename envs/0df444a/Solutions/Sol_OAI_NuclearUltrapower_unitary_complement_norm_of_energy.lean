-- Prove2me | solution 1 for OAI.NuclearUltrapower.unitary_complement_norm_of_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:01:36.574865+00:00
-- url     : https://prove2.me/submissions/55a7922e-44c6-4930-b397-9a7c8646f5b3

import Mathlib
import Definitions.Def_OAIQ019N028

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Laplacian
attribute [-instance] _root_.OAI.NuclearUltrapower.instStarNormUltrapower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace NuclearUltrapower

section Algebra
variable {Γ A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem laplacian_nonneg (S : Finset Γ) (u : Γ → A) : 0 ≤ laplacian S u :=
  Finset.sum_nonneg fun _ _ => star_mul_self_nonneg _

theorem laplacian_selfAdjoint (S : Finset Γ) (u : Γ → A) :
    IsSelfAdjoint (laplacian S u) := IsSelfAdjoint.of_nonneg (laplacian_nonneg S u)

theorem laplacian_le (S : Finset Γ) (u : Γ → unitary A) :
    laplacian S (fun s => (u s : A)) ≤ (4 * (S.card : ℝ)) • (1 : A) := by
  have h (s : Γ) : star ((u s : A) - 1) * ((u s : A) - 1) ≤ (4 : ℝ) • (1 : A) := by
    have hp := star_mul_self_nonneg ((u s : A) + 1)
    have he : (4 : ℝ) • (1:A) - star ((u s : A) - 1) * ((u s : A) - 1) =
        star ((u s : A) + 1) * ((u s : A) + 1) := by
      simp only [star_sub, star_add, star_one, sub_mul, mul_sub, add_mul, mul_add,
        one_mul, mul_one, Unitary.coe_star_mul_self (u s)]
      module
    exact sub_nonneg.mp (he ▸ hp)
  apply (Finset.sum_le_sum fun s _ => h s).trans_eq
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  ring

/-- The norm form used for passing a positive lower bound through nuclearity. -/
theorem laplacian_complement_norm (S : Finset Γ) (u : Γ → unitary A)
    {b : ℝ} (hb : b ≤ 4 * (S.card : ℝ))
    (hgap : b • (1:A) ≤ laplacian S (fun s => (u s : A))) :
    ‖(4 * (S.card : ℝ)) • (1:A) - laplacian S (fun s => (u s : A))‖ ≤
      4 * (S.card : ℝ) - b := by
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (sub_nonneg.mpr hb)
    (sub_nonneg.mpr (laplacian_le S u))).mpr
  rw [Algebra.algebraMap_eq_smul_one, sub_smul]
  exact sub_le_sub_left hgap _

end Algebra

section Operator
variable {Γ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The quadratic form is exactly the energy, with no representation relations. -/
theorem laplacian_inner (S : Finset Γ) (u : Γ → (H →L[ℂ] H)) (x : H) :
    inner ℂ x (laplacian S u x) = (∑ s ∈ S, ‖u s x - x‖ ^ 2 : ℝ) := by
  simp only [laplacian, sum_apply, inner_sum, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp [inner_self_eq_norm_sq_to_K]

/-- Real quadratic forms detect the operator lower bound. -/
theorem laplacian_lower_iff (S : Finset Γ) (u : Γ → (H →L[ℂ] H)) (b : ℝ) :
    b • (1 : H →L[ℂ] H) ≤ laplacian S u ↔
      ∀ x, b * ‖x‖ ^ 2 ≤ ∑ s ∈ S, ‖u s x - x‖ ^ 2 := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff']
  have hself : IsSelfAdjoint (laplacian S u - b • (1 : H →L[ℂ] H)) :=
    (laplacian_selfAdjoint S u).sub ((IsSelfAdjoint.all b).smul (IsSelfAdjoint.one _))
  rw [and_iff_right hself]
  have hq (x : H) : inner ℂ ((laplacian S u - b • (1 : H →L[ℂ] H)) x) x =
      ((∑ s ∈ S, ‖u s x - x‖ ^ 2 : ℝ) - b * ‖x‖ ^ 2 : ℝ) := by
    calc
      _ = inner ℂ x ((laplacian S u - b • (1 : H →L[ℂ] H)) x) := hself.isSymmetric x x
      _ = _ := by
        simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right,
          inner_smul_right_eq_smul, laplacian_inner, inner_self_eq_norm_sq_to_K]
        simp only [RCLike.real_smul_eq_coe_mul]
        push_cast
        rfl
  have hr (r : ℝ) : (0 : ℂ) ≤ (r : ℂ) ↔ 0 ≤ r := RCLike.ofReal_nonneg (K := ℂ)
  simp only [hq, hr, sub_nonneg]

end Operator
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SpatialGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
noncomputable section
open scoped TensorProduct
noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
open scoped TensorProduct InnerProductSpace ComplexOrder

section SpatialGap
variable {Γ : Type u} [Group Γ] {B C : Type v} [CStarAlgebra B] [CStarAlgebra C]

theorem unitary_complement_norm_of_energy_oai {J T : Type*} [NormedAddCommGroup T]
    [InnerProductSpace ℂ T] [CompleteSpace T] (S : Finset J)
    (U : J → unitary (T →L[ℂ] T)) (b : ℝ) (hb : b ≤ 4 * (S.card : ℝ))
    (he : ∀ x : T, b * ‖x‖ ^ 2 ≤ ∑ s ∈ S, ‖(U s : T →L[ℂ] T) x - x‖ ^ 2) :
    ‖(4 * (S.card : ℂ)) • (1 : T →L[ℂ] T) -
        laplacian S (fun s => (U s : T →L[ℂ] T))‖ ≤ 4 * (S.card : ℝ) - b := by
  have hg := (laplacian_lower_iff S (fun s => (U s : T →L[ℂ] T)) b).mpr he
  have hr (r : ℝ) (a : T →L[ℂ] T) : (r : ℂ) • a = r • a :=
    IsScalarTower.algebraMap_smul ℂ r a
  have hcast : (4 * (S.card : ℂ)) = ((4 * (S.card : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, hr]
  exact laplacian_complement_norm S U hb hg

end SpatialGap
end NuclearUltrapower

end
end
end
end
end
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.NuclearUltrapower.unitary_complement_norm_of_energy_oai.{u_1, u_2} := @OAI.NuclearUltrapower.unitary_complement_norm_of_energy_oai.{u_1, u_2}
