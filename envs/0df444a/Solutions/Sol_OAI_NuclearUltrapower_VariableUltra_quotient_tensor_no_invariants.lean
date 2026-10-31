-- Prove2me | solution 1 for OAI.NuclearUltrapower.VariableUltra.quotient_tensor_no_invariants
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:01:34.311428+00:00
-- url     : https://prove2.me/submissions/bb3aafe4-5467-4476-804e-b73ebe65d2a3

import Mathlib
import Definitions.Def_OAIQ019N041

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
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_VariableUltraproduct
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
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

namespace NuclearUltrapower
namespace VariableUltra
open scoped WithCStarModule

variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)
variable (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]

attribute [local instance] OAI.NuclearUltrapower.VariableUltra.entryOrder
attribute [local instance] OAI.NuclearUltrapower.VariableUltra.entryStarOrder
attribute [local instance] OAI.NuclearUltrapower.VariableUltra.quotientOrder
attribute [local instance] OAI.NuclearUltrapower.VariableUltra.quotientStarOrder
/-- Fixed finite matrix amplification commutes with the quotient, entry by entry. -/
theorem matrixQuotient_injective : Function.Injective (matrixQuotient A ω n) := by
  intro M N h
  induction M using Quotient.inductionOn with | h M =>
    induction N using Quotient.inductionOn with | h N =>
      have he (j k : n) : Rel A ω (matrixEntry A n M j k) (matrixEntry A n N j k) := by
        change @Setoid.r _ (con A ω).toSetoid _ _
        apply Quotient.exact
        exact congrArg (fun q : CStarMatrix n n (Algebra A ω) => q j k) h
      apply Quotient.sound
      apply squeeze_zero (fun _ => norm_nonneg _) (fun i => matrix_norm_le_sum (M i - N i))
      have ht := tendsto_finsetSum Finset.univ (fun k _ =>
        tendsto_finsetSum Finset.univ (fun j _ => he j k))
      simpa only [Rel, matrixEntry_apply, Finset.sum_const_zero, CStarMatrix.sub_apply] using ht

/-- No matrix norm is lost in the entrywise quotient identification. -/
theorem matrixQuotient_norm (M : Algebra (fun i => CStarMatrix n n (A i)) ω) :
    ‖matrixQuotient A ω n M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map _ (matrixQuotient_injective A ω n) M

end VariableUltra
end NuclearUltrapower

namespace NuclearUltrapower

namespace VariableUltra
variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)
variable (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]

attribute [local instance] OAI.NuclearUltrapower.VariableUltra.normEntryOrder
attribute [local instance] OAI.NuclearUltrapower.VariableUltra.normEntryStarOrder
local instance seqOrder_r9c0536_1 : PartialOrder (Seq A) := CStarAlgebra.spectralOrder _
local instance seqStarOrder_r9c0536_1 : StarOrderedRing (Seq A) := CStarAlgebra.spectralOrderedRing _
attribute [local instance] OAI.NuclearUltrapower.VariableUltra.normQuotientOrder
attribute [local instance] OAI.NuclearUltrapower.VariableUltra.normQuotientStarOrder
/-- The norm of each FIXED finite matrix over the quotient is its coordinate
ultralimit. The entry algebras and their dimensions are unrestricted. -/
theorem matrixMap_mk_norm (M : CStarMatrix n n (Seq A)) :
    ‖matrixMap n (mk A ω) M‖ =
      seqNorm (fun i => CStarMatrix n n (A i)) ω (matrixFamily A n M) := by
  rw [← matrixQuotient_matrixFamily, matrixQuotient_norm, mk_norm]

/-- Finite exceptional coordinates can be discarded before amplification. -/
theorem matrixMap_mk_norm_le (M : CStarMatrix n n (Seq A)) {C : ℝ}
    (h : ∀ᶠ i in (ω : Filter ι), ‖matrixFamily A n M i‖ ≤ C) :
    ‖matrixMap n (mk A ω) M‖ ≤ C := by
  rw [matrixMap_mk_norm]
  exact le_of_tendsto (seqNorm_tendsto _ ω _) h

end VariableUltra
end NuclearUltrapower

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_TensorGap
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.instStarRingNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional
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

namespace NuclearUltrapower

namespace VariableUltra
variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)

variable (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]
attribute [local instance] OAI.NuclearUltrapower.VariableUltra.gapEntryOrder
attribute [local instance] OAI.NuclearUltrapower.VariableUltra.gapSeqOrder
local instance gapSeqStarOrder : StarOrderedRing (Seq A) := CStarAlgebra.spectralOrderedRing _

attribute [local instance] OAI.NuclearUltrapower.VariableUltra.gapEntryStarOrder
attribute [local instance] OAI.NuclearUltrapower.VariableUltra.gapQuotientOrder
attribute [local instance] OAI.NuclearUltrapower.VariableUltra.gapQuotientStarOrder
/-- Fixed-size polynomial transfer, with only an EVENTUAL coordinate bound. -/
theorem coefficient_complement_quotient_bound {Γ : Type*} (S : Finset Γ)
    (u : Γ → Seq A) (c : Γ → n → n → ℂ) (R C : ℝ)
    (h : ∀ᶠ i in (ω : Filter ι),
      ‖R • (1 : CStarMatrix n n (A i)) -
        laplacian S (fun s => coefficientMatrix (c s) (u s i))‖ ≤ C) :
    ‖R • (1 : CStarMatrix n n (Algebra A ω)) -
      laplacian S (fun s => coefficientMatrix (c s) (mk A ω (u s)))‖ ≤ C := by
  let M : CStarMatrix n n (Seq A) := R • (1 : CStarMatrix n n (Seq A)) -
    laplacian S (fun s => coefficientMatrix (c s) (u s))
  have hmap : matrixMap n (mk A ω) M =
      R • (1 : CStarMatrix n n (Algebra A ω)) -
        laplacian S (fun s => coefficientMatrix (c s) (mk A ω (u s))) := by
    calc
      _ = R • (1 : CStarMatrix n n (Algebra A ω)) -
          laplacian S (fun s => matrixMap n (mk A ω) (coefficientMatrix (c s) (u s))) :=
        map_laplacian_complement (matrixMap n (mk A ω)) S _ R
      _ = _ := by simp only [matrixMap_coefficientMatrix]
  rw [← hmap]
  apply matrixMap_mk_norm_le
  filter_upwards [h] with i hi
  rw [matrixFamily_eval]
  have hmi : matrixMap n (eval A i) M =
      R • (1 : CStarMatrix n n (A i)) -
        laplacian S (fun s => coefficientMatrix (c s) (u s i)) := by
    have hs : matrixMap n (eval A i) (R • (1 : CStarMatrix n n (Seq A))) =
        R • matrixMap n (eval A i) 1 :=
      (matrixMap n (eval A i)).toAlgHom.map_smul_of_tower _ _
    dsimp only [M]
    rw [map_sub, hs]
    simp only [map_one, map_laplacian, matrixMap_coefficientMatrix, eval_apply]
  rw [hmi]
  exact hi

end VariableUltra
end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct
section NoInvariant
variable {Γ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strict complemented-norm gap excludes every common fixed vector. -/
theorem no_invariant_of_complement_norm (S : Finset Γ) (a : Γ → (H →L[ℂ] H))
    {κ : ℝ} (hκ : 0 < κ)
    (h : ‖(4 * (S.card : ℝ)) • (1 : H →L[ℂ] H) - laplacian S a‖ ≤
      4 * (S.card : ℝ) - κ) (x : H) (hx : ∀ s ∈ S, a s x = x) : x = 0 := by
  have hxL : laplacian S a x = 0 := by
    simp only [laplacian, sum_apply, mul_apply_eq_comp]
    apply Finset.sum_eq_zero
    intro s hs
    rw [sub_apply, one_apply_eq_self, hx s hs, sub_self, map_zero]
  have hh := ((4 * (S.card : ℝ)) • (1 : H →L[ℂ] H) - laplacian S a).le_opNorm x
  rw [sub_apply, smul_apply, one_apply_eq_self, hxL, sub_zero, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ 4 * (S.card : ℝ))] at hh
  have hbound := hh.trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg x]
end NoInvariant

namespace VariableUltra
variable {ι : Type u} (E : ι → Type v)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)] (ω : Ultrafilter ι)

variable {K F : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

attribute [local instance] OAI.NuclearUltrapower.VariableUltra.operatorQuotientOrder
local instance operatorQuotientStarOrder : StarOrderedRing (operatorQuotient E ω) :=
  CStarAlgebra.spectralOrderedRing _

/-- The strict coordinate tensor gap survives in EVERY unital representation
of the varying matrix quotient. No faithfulness is needed here. -/
theorem quotient_tensor_complement_bound {Γ : Type*} (S : Finset Γ)
    (b : OrthonormalBasis n ℂ F) (U : ∀ i, Γ → (E i ≃ₗᵢ[ℂ] E i))
    (V : Γ → (F ≃ₗᵢ[ℂ] F)) {κ : ℝ} (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : ∀ᶠ i in (ω : Filter ι), ∀ z : E i ⊗[ℂ] F,
      κ * ‖z‖ ^ 2 ≤ ∑ s ∈ S, ‖TensorProduct.congrIsometry (U i s) (V s) z - z‖ ^ 2)
    (φ : operatorQuotient E ω →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    ‖(4 * (S.card : ℝ)) • (1 : CStarMatrix n n (K →L[ℂ] K)) -
      laplacian S (fun s => tensorOperatorMatrix b
        (representedIso E ω φ (fun i => U i s)) (V s))‖ ≤ 4 * (S.card : ℝ) - κ := by
  let u : Γ → operatorSeq E := fun s => (isoSequence E (fun i => U i s) : operatorSeq E)
  let c : Γ → n → n → ℂ := fun s j k => b.repr (V s (b k)) j
  have hcoord : ∀ᶠ i in (ω : Filter ι),
      ‖(4 * (S.card : ℝ)) • (1 : CStarMatrix n n (E i →L[ℂ] E i)) -
        laplacian S (fun s => coefficientMatrix (c s) (u s i))‖ ≤ 4 * (S.card : ℝ) - κ := by
    filter_upwards [hgap] with i hi
    exact tensorMatrix_complement_bound S b (U i) V hκ hi
  have hQ := coefficient_complement_quotient_bound (fun i => E i →L[ℂ] E i) ω n S u c
    (4 * (S.card : ℝ)) (4 * (S.card : ℝ) - κ) hcoord
  have hφ := (NonUnitalStarAlgHom.norm_apply_le (matrixMap n φ).toNonUnitalStarAlgHom
    ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n (operatorQuotient E ω)) -
      laplacian S (fun s => coefficientMatrix (c s) (mk _ ω (u s))))).trans hQ
  change ‖matrixMap n φ _‖ ≤ _ at hφ
  have he : matrixMap n φ
      ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n (operatorQuotient E ω)) -
        laplacian S (fun s => coefficientMatrix (c s) (mk _ ω (u s)))) =
      (4 * (S.card : ℝ)) • (1 : CStarMatrix n n (K →L[ℂ] K)) -
        laplacian S (fun s => coefficientMatrix (c s) (φ (mk _ ω (u s)))) := by
    have hs : matrixMap n φ ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n (operatorQuotient E ω))) =
        (4 * (S.card : ℝ)) • matrixMap n φ 1 :=
      (matrixMap n φ).toAlgHom.map_smul_of_tower _ _
    rw [map_sub, hs]
    simp only [map_one, map_laplacian, matrixMap_coefficientMatrix]
  rw [he] at hφ
  exact hφ

/-- In particular a tensor intertwiner in a quotient representation must vanish. -/
theorem quotient_tensor_no_invariants_oai {Γ : Type*} (S : Finset Γ)
    (b : OrthonormalBasis n ℂ F) (U : ∀ i, Γ → (E i ≃ₗᵢ[ℂ] E i))
    (V : Γ → (F ≃ₗᵢ[ℂ] F)) {κ : ℝ} (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : ∀ᶠ i in (ω : Filter ι), ∀ z : E i ⊗[ℂ] F,
      κ * ‖z‖ ^ 2 ≤ ∑ s ∈ S, ‖TensorProduct.congrIsometry (U i s) (V s) z - z‖ ^ 2)
    (φ : operatorQuotient E ω →⋆ₐ[ℂ] (K →L[ℂ] K))
    (z : K ⊗[ℂ] F)
    (hz : ∀ s ∈ S, TensorProduct.congrIsometry
      (representedIso E ω φ (fun i => U i s)) (V s) z = z) : z = 0 := by
  have hm := quotient_tensor_complement_bound E ω S b U V hκ hgap φ
  let u : Γ → (PiLp 2 (fun _ : n => K) →L[ℂ] PiLp 2 (fun _ : n => K)) :=
    fun s => tensorPiUnitary b (representedIso E ω φ (fun i => U i s)) (V s)
  have hnorm : ‖(4 * (S.card : ℝ)) • (1 : PiLp 2 (fun _ : n => K) →L[ℂ] PiLp 2 (fun _ : n => K)) -
      laplacian S u‖ ≤ 4 * (S.card : ℝ) - κ := by
    have ha := (NonUnitalStarAlgHom.norm_apply_le
      (operatorMatrixActionHom (n := n) (H := K)).toNonUnitalStarAlgHom _).trans hm
    change ‖operatorMatrixActionHom (n := n) (H := K) _‖ ≤ _ at ha
    have he : operatorMatrixActionHom (n := n) (H := K)
        ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n (K →L[ℂ] K)) -
          laplacian S (fun s => tensorOperatorMatrix b
            (representedIso E ω φ (fun i => U i s)) (V s))) =
        (4 * (S.card : ℝ)) • (1 : PiLp 2 (fun _ : n => K) →L[ℂ] PiLp 2 (fun _ : n => K)) -
          laplacian S u := by
      have hs : operatorMatrixActionHom (n := n) (H := K)
          ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n (K →L[ℂ] K))) =
          (4 * (S.card : ℝ)) • operatorMatrixActionHom (n := n) (H := K) 1 :=
        (operatorMatrixActionHom (n := n) (H := K)).toAlgHom.map_smul_of_tower _ _
      rw [map_sub, hs]
      simp only [map_one, laplacian, map_sum, map_mul, map_star, map_sub,
        tensorOperatorMatrix_conjugacy]
      rfl
    rw [he] at ha
    exact ha
  have hy := no_invariant_of_complement_norm S u hκ0 hnorm (tensorPiIsometry b z) (by
    intro s hs
    change tensorPiUnitary _ _ _ (tensorPiIsometry b z) = _
    rw [tensorPiUnitary_apply_tensorPi, hz s hs])
  exact (tensorPiIsometry b).injective (by simpa using hy)
end VariableUltra
end NuclearUltrapower

end
end
end
end
end

end OAI
end

theorem solution.{u, v, u_1, u_2, u_3, u_4} : type_of% @OAI.NuclearUltrapower.VariableUltra.quotient_tensor_no_invariants_oai.{u, v, u_1, u_2, u_3, u_4} := @OAI.NuclearUltrapower.VariableUltra.quotient_tensor_no_invariants_oai.{u, v, u_1, u_2, u_3, u_4}
