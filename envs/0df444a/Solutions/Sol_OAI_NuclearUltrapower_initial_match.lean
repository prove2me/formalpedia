-- Prove2me | solution 1 for OAI.NuclearUltrapower.initial_match
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T14:34:21.1834+00:00
-- url     : https://prove2.me/submissions/49d55c37-e74c-4ab6-ae2e-7e0712126619

import Mathlib
import Definitions.Def_OAIQ019N043
import Theorems.Thm_OAI_NuclearUltrapower_not_matches_coefficient_bound

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_VariableUltraproduct
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
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
local instance seqOrder_r752742_1 : PartialOrder (Seq A) := CStarAlgebra.spectralOrder _
local instance seqStarOrder_r752742_1 : StarOrderedRing (Seq A) := CStarAlgebra.spectralOrderedRing _
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
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
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

end NuclearUltrapower

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_InitialMatching
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
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

end NuclearUltrapower
end
end

section

noncomputable section
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v
section Obstruction
variable {Γ A K F : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  (S : Finset Γ) (w : Γ → A) (ψ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
  (σ : Γ → K ≃ₗᵢ[ℂ] K) (π : Γ → F ≃ₗᵢ[ℂ] F)
  {n : Type*} [Fintype n] [DecidableEq n] (b : OrthonormalBasis n ℂ F)

attribute [local instance] OAI.NuclearUltrapower.instPartialOrder_solutions_1
attribute [local instance] OAI.NuclearUltrapower.instStarOrderedRing_solutions_1
/-- The full algebra can see an invariant tensor in any representation. A
strict complemented-matrix bound would exclude that tensor. -/
theorem coefficient_bound_no_invariant (hψ : ∀ g, ψ (w g) = (σ g : K →L[ℂ] K))
    (a : ℝ) (ha : 0 < a)
    (hb : ‖(4 * (S.card : ℝ)) • (1 : CStarMatrix n n A) -
      laplacian S (fun s => coefficientMatrix (fun i j => b.repr (π s (b j)) i) (w s))‖ ≤
        4 * (S.card : ℝ) - a)
    (z : K ⊗[ℂ] F) (hz : ∀ s ∈ S, TensorProduct.congrIsometry (σ s) (π s) z = z) : z = 0 := by
  let M : CStarMatrix n n A := (4 * (S.card : ℝ)) • 1 -
    laplacian S (fun s => coefficientMatrix (fun i j => b.repr (π s (b j)) i) (w s))
  let Ψ := (operatorMatrixActionHom (n := n) (H := K)).comp (matrixMap n ψ)
  have he : Ψ M = (4 * (S.card : ℝ)) • (1 : PiLp 2 (fun _ : n => K) →L[ℂ] PiLp 2 (fun _ : n => K)) -
      laplacian S (fun s => (tensorPiUnitary b (σ s) (π s) :
        PiLp 2 (fun _ : n => K) →L[ℂ] PiLp 2 (fun _ : n => K))) := by
    dsimp only [M]
    rw [map_sub, show Ψ ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n A)) =
      (4 * (S.card : ℝ)) • Ψ 1 from Ψ.toAlgHom.map_smul_of_tower _ _]
    simp only [map_one, map_laplacian]
    congr 1
    apply congrArg (laplacian S)
    funext s
    change operatorMatrixActionHom (n := n) (H := K)
      (matrixMap n ψ (coefficientMatrix (fun i j => b.repr (π s (b j)) i) (w s))) = _
    rw [matrixMap_coefficientMatrix, hψ]
    exact tensorOperatorMatrix_conjugacy b (σ s) (π s)
  have hbound := (NonUnitalStarAlgHom.norm_apply_le Ψ M).trans hb
  rw [he] at hbound
  have hez := no_invariant_of_complement_norm S
    (fun s => (tensorPiUnitary b (σ s) (π s) :
      PiLp 2 (fun _ : n => K) →L[ℂ] PiLp 2 (fun _ : n => K))) ha hbound
      (tensorPiIsometry b z) (by
        intro s hs
        change tensorPiUnitary b (σ s) (π s) (tensorPiIsometry b z) = _
        rw [tensorPiUnitary_apply_tensorPi, hz s hs])
  exact (tensorPiIsometry b).injective (hez.trans (map_zero _).symm)
end Obstruction
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u
section InitialMatch
variable {Γ A B E K : Type u} [Group Γ] [CStarAlgebra A] [CStarAlgebra B] [Nontrivial B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (hρ : Function.Injective ρ)
  (S : Finset Γ) (ω : Ultrafilter ℕ)
  (φ : A →⋆ₐ[ℂ] VariableUltra.Algebra (fun _ : ℕ => B) ω) (hφ : Function.Injective φ)
  (w : Γ → A) (u : Γ → ℕ → unitary B)
  (hu : ∀ g, φ (w g) = VariableUltra.mk (fun _ : ℕ => B) ω
    (VariableUltra.unitarySequence (fun _ : ℕ => B) (u g)))
  (ψ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (σ : Γ → K ≃ₗᵢ[ℂ] K)
  (hψ : ∀ g, ψ (w g) = (σ g : K →L[ℂ] K))
local instance instPartialOrder_solutions_2_r752742_1 : PartialOrder A := CStarAlgebra.spectralOrder A
local instance instStarOrderedRing_solutions_2_r752742_1 : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
attribute [local instance] OAI.NuclearUltrapower.instPartialOrder_solutions_3
local instance instStarOrderedRing_solutions_3 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
attribute [local instance] OAI.NuclearUltrapower.instPartialOrderAlgebraNat
local instance instStarOrderedRingAlgebraNat : StarOrderedRing (VariableUltra.Algebra (fun _ : ℕ => B) ω) :=
  CStarAlgebra.spectralOrderedRing _

include hρ hu hφ hψ in
/-- A full-algebra invariant tensor forces matching on an ultrafilter-large
set. This is fixed-size matrix amplification, not an illicit varying-size one. -/
theorem initial_match_oai (π : FiniteUnitaryRep.{u,u} Γ) (a : ℝ)
    (ha0 : 0 < a) (ha : a ≤ 4 * (S.card : ℝ))
    (z : K ⊗[ℂ] π) (hz0 : z ≠ 0)
    (hz : ∀ s ∈ S, TensorProduct.congrIsometry (σ s) (π.action s) z = z) :
    ∀ᶠ n in (ω : Filter ℕ), Matches ρ S (fun g => u g n) a π := by
  classical
  by_contra hm
  have hn := (ω.eventually_not).mpr hm
  let b := stdOrthonormalBasis ℂ π
  let n := Fin (Module.finrank ℂ π)
  let : Nonempty n := ⟨⟨0,Module.finrank_pos⟩⟩
  let c : Γ → n → n → ℂ := fun s i j => b.repr (π.action s (b j)) i
  have hb : ∀ᶠ i in (ω : Filter ℕ),
      ‖(4 * (S.card : ℝ)) • (1 : CStarMatrix n n B) -
        laplacian S (fun s => coefficientMatrix (c s) (u s i : B))‖ ≤
          4 * (S.card : ℝ) - a := by
    filter_upwards [hn] with i hi
    exact not_matches_coefficient_bound ρ S (fun g => u g i) hρ π b a ha hi
  have hq := VariableUltra.coefficient_complement_quotient_bound (fun _ : ℕ => B) ω n S
    (fun g => (VariableUltra.unitarySequence (fun _ : ℕ => B) (u g) : VariableUltra.Seq (fun _ : ℕ => B)))
      c (4 * (S.card : ℝ)) (4 * (S.card : ℝ) - a) hb
  let M : CStarMatrix n n A := (4 * (S.card : ℝ)) • 1 -
    laplacian S (fun s => coefficientMatrix (c s) (w s))
  have hmap : matrixMap n φ M = (4 * (S.card : ℝ)) •
      (1 : CStarMatrix n n (VariableUltra.Algebra (fun _ : ℕ => B) ω)) -
      laplacian S (fun s => coefficientMatrix (c s)
        (VariableUltra.mk (fun _ : ℕ => B) ω
          (VariableUltra.unitarySequence (fun _ : ℕ => B) (u s)))) := by
    dsimp only [M]
    rw [map_sub, show matrixMap n φ ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n A)) =
      (4 * (S.card : ℝ)) • matrixMap n φ 1 from (matrixMap n φ).toAlgHom.map_smul_of_tower _ _]
    simp only [map_one, map_laplacian]
    simp only [matrixMap_coefficientMatrix, hu]
  have hnorm := NonUnitalStarAlgHom.norm_map (matrixMap n φ).toNonUnitalStarAlgHom
    (matrixMap_injective n φ hφ) M
  have hmnorm : ‖M‖ ≤ 4 * (S.card : ℝ) - a := by
    apply hnorm.symm.le.trans
    change ‖matrixMap n φ M‖ ≤ _
    rw [hmap]
    exact hq
  exact hz0 (coefficient_bound_no_invariant S w ψ σ π.action b hψ a ha0 hmnorm z hz)
end InitialMatch
end NuclearUltrapower
end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.NuclearUltrapower.initial_match_oai.{u} := @OAI.NuclearUltrapower.initial_match_oai.{u}
