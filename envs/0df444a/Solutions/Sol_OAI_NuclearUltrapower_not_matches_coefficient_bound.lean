-- Prove2me | solution 1 for OAI.NuclearUltrapower.not_matches_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T14:36:14.089932+00:00
-- url     : https://prove2.me/submissions/4c6c3a13-1b15-4d97-9bee-b3cffed3eaa5

import Mathlib
import Definitions.Def_OAIQ019N043

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Laplacian
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
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
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_TensorGap
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional
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
namespace NuclearUltrapower

section MatrixAction
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- One-column vectors recover every coefficient; amplification is faithful. -/
theorem operatorMatrixActionHom_injective : Function.Injective (operatorMatrixActionHom (n := n) (H := H)) := by
  intro M N h
  apply CStarMatrix.ext
  intro i j
  ext x
  have he := congrArg (fun T : PiLp 2 (fun _ : n => H) →L[ℂ] PiLp 2 (fun _ : n => H) =>
    T (PiLp.single 2 j x) i) h
  simpa [operatorMatrixActionHom_apply, PiLp.single_apply, apply_ite] using he

end MatrixAction

open scoped TensorProduct
section TensorMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Entry-by-entry compatibility of the operator tensor with matrix amplification. -/
theorem tensorOperatorMatrix_action [CompleteSpace E] (b : OrthonormalBasis n ℂ F)
    (U : E →L[ℂ] E) (V : F →L[ℂ] F) (z : E ⊗[ℂ] F) :
    operatorMatrixActionHom (n := n) (H := E) (tensorOperatorMatrix b U V) (tensorPiIsometry b z) =
      tensorPiIsometry b (TensorProduct.mapL U V z) := by
  induction z using OAI.tensorInductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul x y =>
    ext i
    simp only [operatorMatrixActionHom_apply, tensorOperatorMatrix_apply, smul_apply,
      tensorPiIsometry_tmul, map_smul, TensorProduct.mapL_tmul, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    have h := congrArg (fun v : F => b.repr (V v) i) (b.sum_repr y)
    simpa only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
      WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, mul_comm] using h

end TensorMatrix
end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct
section MatrixGap
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem tensorOperatorMatrix_conjugacy (b : OrthonormalBasis n ℂ F)
    (U : E ≃ₗᵢ[ℂ] E) (V : F ≃ₗᵢ[ℂ] F) :
    operatorMatrixActionHom (n := n) (H := E) (tensorOperatorMatrix b U V) =
      (tensorPiUnitary b U V : PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => E)) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := (tensorPiIsometry b).surjective x
  change operatorMatrixActionHom (n := n) (H := E) (tensorOperatorMatrix b U V)
    (tensorPiIsometry b z) = tensorPiUnitary b U V (tensorPiIsometry b z)
  rw [tensorOperatorMatrix_action, tensorPiUnitary_apply_tensorPi]
  congr 1
  simp only [TensorProduct.mapL_apply, TensorProduct.congrIsometry_apply]
  rfl

/-- Fixed-factor matrix norms see precisely the tensor Kazhdan estimate. -/
theorem tensorMatrix_complement_bound {Γ : Type*} (S : Finset Γ)
    (b : OrthonormalBasis n ℂ F) (U : Γ → (E ≃ₗᵢ[ℂ] E)) (V : Γ → (F ≃ₗᵢ[ℂ] F))
    {κ : ℝ} (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : ∀ z : E ⊗[ℂ] F, κ * ‖z‖ ^ 2 ≤
      ∑ s ∈ S, ‖TensorProduct.congrIsometry (U s) (V s) z - z‖ ^ 2) :
    ‖(4 * (S.card : ℝ)) • (1 : CStarMatrix n n (E →L[ℂ] E)) -
      laplacian S (fun s => tensorOperatorMatrix b (U s) (V s))‖ ≤
        4 * (S.card : ℝ) - κ := by
  let u : Γ → unitary (PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => E)) :=
    fun s => Unitary.linearIsometryEquiv.symm (tensorPiUnitary b (U s) (V s))
  have hPi : κ • (1 : PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => E)) ≤
      laplacian S (fun s => (u s : PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => E))) := by
    rw [laplacian_lower_iff]
    intro x
    obtain ⟨z, rfl⟩ := (tensorPiIsometry b).surjective x
    have hd (s : Γ) : (u s : PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => E))
        (tensorPiIsometry b z) - tensorPiIsometry b z =
        tensorPiIsometry b (TensorProduct.congrIsometry (U s) (V s) z - z) := by
      change tensorPiUnitary b (U s) (V s) (tensorPiIsometry b z) - _ = _
      simp only [tensorPiUnitary_apply_tensorPi, map_sub]
    simpa only [hd, (tensorPiIsometry b).norm_map] using hgap z
  have hbound := laplacian_complement_norm S u hκ hPi
  have hmap : operatorMatrixActionHom (n := n) (H := E)
      ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n (E →L[ℂ] E)) -
        laplacian S (fun s => tensorOperatorMatrix b (U s) (V s))) =
      (4 * (S.card : ℝ)) • (1 : PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => E)) -
        laplacian S (fun s => (u s : PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => E))) := by
    have hs : operatorMatrixActionHom (n := n) (H := E)
        ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n (E →L[ℂ] E))) =
        (4 * (S.card : ℝ)) • operatorMatrixActionHom (n := n) (H := E) 1 :=
      (operatorMatrixActionHom (n := n) (H := E)).toAlgHom.map_smul_of_tower _ _
    rw [map_sub, hs]
    simp only [map_one, laplacian, map_sum, map_mul, map_star, map_sub,
      tensorOperatorMatrix_conjugacy]
    rfl
  rw [← hmap] at hbound
  exact (NonUnitalStarAlgHom.norm_map
    (operatorMatrixActionHom (n := n) (H := E)).toNonUnitalStarAlgHom
    (operatorMatrixActionHom_injective (n := n) (H := E)) _).symm.le.trans hbound
end MatrixGap
end NuclearUltrapower

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_NuclearFiniteness
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u v w
open Filter
open scoped Topology InnerProductSpace ENNReal

noncomputable section

open scoped InnerProductSpace Topology
open Filter

namespace NuclearUltrapower
variable {Γ : Type u} {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem tupleEnergy_smul (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) (c : ℂ) (x : E) :
    tupleEnergy S U (c • x) = ‖c‖ ^ 2 * tupleEnergy S U x := by
  simp only [tupleEnergy, map_smul, ← smul_sub, norm_smul, mul_pow, Finset.mul_sum]

end NuclearUltrapower

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_TensorMatching
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v
section MatchSubrep
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)

omit [Nontrivial E] in
/-- Normalized and homogeneous strict Rayleigh inequalities agree. -/
theorem matches_iff_homogeneous (a : ℝ) (π : FiniteUnitaryRep.{u,v} Γ) :
    Matches ρ S u a π ↔ ∃ x : TensorHilbert E π,
      tupleEnergy S (matchingTuple ρ u π) x < a * ‖x‖^2 := by
  constructor
  · rintro ⟨x,hx,he⟩
    exact ⟨x, by simpa only [hx,one_pow,mul_one] using he⟩
  rintro ⟨x,hx⟩
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    simp [tupleEnergy] at hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  refine ⟨(‖x‖⁻¹ : ℂ) • x, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  rw [tupleEnergy_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  have h := mul_lt_mul_of_pos_left hx (sq_pos_of_pos (inv_pos.mpr hn))
  calc
    _ < ‖x‖⁻¹^2 * (a * ‖x‖^2) := h
    _ = a := by field_simp

end MatchSubrep
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_InitialMatching
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v

theorem matrixMap_injective {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (n : Type*) [Fintype n] [DecidableEq n] (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ) :
    Function.Injective (matrixMap n φ) := by
  intro M N h
  ext i j
  exact hφ (congrArg (fun X : CStarMatrix n n B => X i j) h)

section Bounds
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)

theorem matching_energy_coe (π : FiniteUnitaryRep.{u,v} Γ) (z : E ⊗[ℂ] π) :
    tupleEnergy S (matchingTuple ρ u π) (z : TensorHilbert E π) =
      ∑ s ∈ S, ‖TensorProduct.congrIsometry (representedUnitary ρ (u s)) (π.action s) z-z‖^2 := by
  apply Finset.sum_congr rfl
  intro s _
  rw [matchingTuple_coe, ← UniformSpace.Completion.coe_sub,
    UniformSpace.Completion.norm_coe]

attribute [local instance] OAI.NuclearUltrapower.instPartialOrder_solutions
attribute [local instance] OAI.NuclearUltrapower.instStarOrderedRing_solutions
/-- Failure of matching is a matrix norm bound, with no relation imposed on u. -/
theorem not_matches_coefficient_bound_oai (hρ : Function.Injective ρ)
    (π : FiniteUnitaryRep.{u,v} Γ) {n : Type*} [Fintype n] [DecidableEq n]
    (b : OrthonormalBasis n ℂ π) (a : ℝ) (ha : a ≤ 4 * (S.card : ℝ))
    (hm : ¬ Matches ρ S u a π) :
    ‖(4 * (S.card : ℝ)) • (1 : CStarMatrix n n B) -
      laplacian S (fun s => coefficientMatrix (fun i j => b.repr (π.action s (b j)) i) (u s : B))‖
      ≤ 4 * (S.card : ℝ) - a := by
  have he (z : E ⊗[ℂ] π) : a * ‖z‖^2 ≤
      ∑ s ∈ S, ‖TensorProduct.congrIsometry (representedUnitary ρ (u s)) (π.action s) z-z‖^2 := by
    have hh : ¬ ∃ x : TensorHilbert E π,
        tupleEnergy S (matchingTuple ρ u π) x < a * ‖x‖^2 :=
      fun hx => hm ((matches_iff_homogeneous ρ S u a π).mpr hx)
    have hn := not_lt.mp (fun h => hh ⟨(z : TensorHilbert E π), h⟩)
    rwa [matching_energy_coe, UniformSpace.Completion.norm_coe] at hn
  have hb := tensorMatrix_complement_bound S b (fun s => representedUnitary ρ (u s)) π.action ha he
  let M : CStarMatrix n n B := (4 * (S.card : ℝ)) • 1 -
    laplacian S (fun s => coefficientMatrix (fun i j => b.repr (π.action s (b j)) i) (u s : B))
  have hmap : matrixMap n ρ M = (4 * (S.card : ℝ)) •
      (1 : CStarMatrix n n (E →L[ℂ] E)) -
      laplacian S (fun s => tensorOperatorMatrix b (representedUnitary ρ (u s)) (π.action s)) := by
    dsimp only [M]
    rw [map_sub, show matrixMap n ρ ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n B)) =
      (4 * (S.card : ℝ)) • matrixMap n ρ 1 from (matrixMap n ρ).toAlgHom.map_smul_of_tower _ _]
    simp only [map_one, map_laplacian]
    congr 1
    apply congrArg (laplacian S)
    funext s
    rw [matrixMap_coefficientMatrix]
    rfl
  rw [← hmap] at hb
  have hn := NonUnitalStarAlgHom.norm_map (matrixMap n ρ).toNonUnitalStarAlgHom
    (matrixMap_injective n ρ hρ) M
  exact hn.symm.le.trans hb
end Bounds
end NuclearUltrapower
end
end

end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.NuclearUltrapower.not_matches_coefficient_bound_oai.{u, v, u_1} := @OAI.NuclearUltrapower.not_matches_coefficient_bound_oai.{u, v, u_1}
