-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.blockState_operator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:51:31.440637+00:00
-- url     : https://prove2.me/submissions/6806137f-bf28-4d6a-acec-ee8dd09758e0

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean:L658-L686
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.blockState_operator. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation
import Theorems.Thm_OAI_FiniteBlock_exp_spectral

-- ---- from OAI.InformationTheory.PhotonNumber.FiniteVariation ----
namespace OAI

noncomputable section

section
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix

namespace FiniteBlock

section
variable {I J E : Type*} [Fintype I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (b : HilbertBasis (I ⊕ J) ℂ E) (c : OrthonormalBasis I ℂ (EuclideanSpace ℂ I))

variable [CompleteSpace E]

omit [CompleteSpace E] in
theorem inner_basis_embed (i : I) (x : EuclideanSpace ℂ I) :
    inner ℂ (b (Sum.inl i)) (embed b x) = x i := by
  classical
  simp [embed_apply, orthonormal_iff_ite.mp b.orthonormal]

omit [CompleteSpace E] in
theorem block_embed (M : Matrix I I ℂ) (x : EuclideanSpace ℂ I) :
    block b M (embed b x) = embed b (WithLp.toLp 2 (M *ᵥ ⇑x)) := by
  classical
  simp only [block, sum_apply, smul_apply,
    InnerProductSpace.rankOne_apply, inner_basis_embed, smul_smul]
  rw [embed_apply]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul]

omit [CompleteSpace E] in
theorem block_tail (M : Matrix I I ℂ) (j : J) : block b M (b (Sum.inr j)) = 0 := by
  classical
  simp [block, InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal]

variable [DecidableEq I]

end

open NormedSpace Matrix
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exp_eigenvector (M : Matrix I I ℂ) (hM : M.IsHermitian) (i : I) :
    exp M *ᵥ ⇑(hM.eigenvectorBasis i) =
      (Real.exp (hM.eigenvalues i) : ℂ) • ⇑(hM.eigenvectorBasis i) := by
  rw [exp_spectral M hM, ← Matrix.mulVec_mulVec, hM.star_eigenvectorUnitary_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.diagonal_mulVec_single]
  rw [show (Real.exp (hM.eigenvalues i) : ℂ)*1 =
    (Real.exp (hM.eigenvalues i) : ℂ) • (1:ℂ) by rfl,
    Pi.single_smul, Matrix.mulVec_smul, hM.eigenvectorUnitary_mulVec]

end FiniteBlock

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I J : Type*}

variable [CompleteSpace E]

end QuantumTrace

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber

section
open TraceEnsemble

end

open QuantumTrace TraceEnsemble

end EntropyPhotonNumber

namespace FiniteBlock

section
open QuantumTrace
variable {I J E K : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end EntropyPhotonNumber

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator

namespace FiniteBlock
variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem block_exp_eigen (b : HilbertBasis (I ⊕ J) ℂ E) (M : Matrix I I ℂ)
    (hM : M.IsHermitian) (i : I) :
    block b (exp M) (basis b hM.eigenvectorBasis (Sum.inl i)) =
      (Real.exp (hM.eigenvalues i) : ℂ) • basis b hM.eigenvectorBasis (Sum.inl i) := by
  rw [basis_inl, block_embed, exp_eigenvector M hM i]
  simp only [WithLp.toLp_smul, WithLp.toLp_ofLp]
  change embed b ((Real.exp (hM.eigenvalues i) : ℂ) • hM.eigenvectorBasis i) = _
  exact map_smul (embed b) _ _

omit [CompleteSpace E] in
 theorem reference_on_block (b : HilbertBasis (I ⊕ J) ℂ E) (p : I ⊕ J → ℝ)
    (T : E →L[ℂ] E) (he : ∀ j, T (b j) = (p j : ℂ) • b j)
    (x : EuclideanSpace ℂ I) :
    T (embed b x) = block b (Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ))) (embed b x) := by
  rw [block_embed, embed_apply b x, map_sum, embed_apply]
  simp only [map_smul, he, smul_smul]
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, ite_mul, mul_comm]

end FiniteBlock

namespace EntropyPhotonNumber

section
open QuantumTrace TraceEnsemble
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

 theorem blockState_operator (ρ : State n) (b : HilbertBasis (I ⊕ J) ℂ (Fock n))
    (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    (blockState b p hp hs M hM).op = ((FiniteBlock.partition p M hM : ℂ)⁻¹) •
      (ρ.op+FiniteBlock.block b (exp M)-FiniteBlock.block b (Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ)))) := by
  let a := FiniteBlock.basis b hM.eigenvectorBasis
  apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr a.dense_span)
  rintro _ ⟨j,rfl⟩
  change (spectralState a _ _ _).op (a j) = _
  rw [spectralState_eigen]
  simp only [smul_apply, sub_apply, add_apply]
  cases j with
  | inl i =>
    have ht : ρ.op (a (Sum.inl i)) =
        FiniteBlock.block b (Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ))) (a (Sum.inl i)) := by
      simpa only [a, FiniteBlock.basis_inl] using
        FiniteBlock.reference_on_block b p ρ.op he (hM.eigenvectorBasis i)
    rw [ht, add_sub_cancel_left]
    rw [FiniteBlock.block_exp_eigen b M hM i, smul_smul]
    congr 1
    simp only [FiniteBlock.weights, Sum.elim_inl]
    push_cast
    ring
  | inr j =>
    simp only [a, FiniteBlock.basis_inr, he, FiniteBlock.block_tail, add_zero, sub_zero,
      smul_smul, FiniteBlock.weights, Sum.elim_inr]
    push_cast
    congr 1
    ring

end

section
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end

open QuantumTrace TraceEnsemble
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end EntropyPhotonNumber

end

section
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace

namespace QuantumCalculus

section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance] OAI.QuantumCalculus.instNormedAlgebraRat_oAI
end

section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
attribute [local instance] OAI.QuantumCalculus.instNormedAlgebraRat_oAI_1
end

section
open scoped Matrix.Norms.Operator ComplexConjugate
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

end

section
open Filter Asymptotics

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
attribute [local instance] OAI.QuantumCalculus.instNormedAlgebraRat_oAI_2
end

section
open Matrix Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

end

section
open Filter Asymptotics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
attribute [local instance] OAI.QuantumCalculus.instNormedAlgebraRat_oAI_3
end

open Matrix Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

end QuantumCalculus

namespace FiniteBlock
open QuantumCalculus
variable {I J : Type*} [Fintype I] [DecidableEq I]

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumCalculus QuantumTrace Filter Asymptotics
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end EntropyPhotonNumber

namespace FiniteBlock
variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end EntropyPhotonNumber

namespace QuantumCalculus
open Matrix Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

end QuantumCalculus

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open Filter Asymptotics Topology

namespace QuantumCalculus

end QuantumCalculus

end

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open Filter Asymptotics Topology
open ContinuousLinearMap

namespace EntropyPhotonNumber

section
open QuantumTrace TraceEnsemble
variable {n : ℕ}

end

section
open QuantumCalculus QuantumTrace Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end

open QuantumCalculus QuantumTrace Filter Asymptotics

end EntropyPhotonNumber

namespace FiniteBlock
open DiagonalForms.System
variable {I J : Type*} [Fintype I]
end FiniteBlock

namespace EntropyPhotonNumber
open QuantumCalculus QuantumTrace Filter Asymptotics
open scoped Matrix.Norms.Operator

end EntropyPhotonNumber

namespace FiniteBlock
open DiagonalForms.System
open scoped ComplexConjugate
variable {I J : Type*} [Fintype I]

end FiniteBlock

namespace BKM
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end BKM

namespace EntropyPhotonNumber

section
open QuantumTrace DiagonalForms.System
open scoped ComplexConjugate
variable {n : ℕ} {J K L : Type*} [Fintype K] [DecidableEq K]

end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {K L : Type*} [Fintype K] [DecidableEq K]

end EntropyPhotonNumber

namespace BKM
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

end BKM

namespace Complex
open scoped _root_.Complex
open scoped ComplexConjugate
end Complex

namespace BKM

section
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
end

section
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

end

open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end BKM

namespace EntropyPhotonNumber

section
open scoped ComplexConjugate ComplexStarModule
variable {n : ℕ} {J : Type*}

end

section
open QuantumTrace DiagonalForms.System
open scoped ComplexStarModule
variable {n : ℕ} {K L J : Type*} [Fintype K] [DecidableEq K]

end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J K L : Type*} [Fintype K] [DecidableEq K]
end EntropyPhotonNumber

namespace BKM
open scoped BigOperators
open DiagonalForms.System
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end BKM

namespace EntropyPhotonNumber
open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J : Type*} [DecidableEq J]

end EntropyPhotonNumber

namespace BKM

section
open scoped BigOperators ComplexConjugate
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

end BKM

namespace CenteredTests
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
end CenteredTests

namespace EntropyPhotonNumber

section
open QuantumTrace DiagonalForms.System
variable {n : ℕ} {I J : Type*} [DecidableEq J]

end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J : Type*} [DecidableEq J]
end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace
namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end GibbsData
end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open QuantumTrace TraceEnsemble


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.blockState_operator := @_root_.OAI.EntropyPhotonNumber.blockState_operator
