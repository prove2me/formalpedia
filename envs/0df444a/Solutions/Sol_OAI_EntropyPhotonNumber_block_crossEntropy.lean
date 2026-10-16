-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.block_crossEntropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:53:07.248365+00:00
-- url     : https://prove2.me/submissions/3bbb42f5-d198-463b-aba4-1830829164a9

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean:L694-L743
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.block_crossEntropy. The node keeps its source
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
import Theorems.Thm_OAI_QuantumTrace_hasSum_trace_basis
import Theorems.Thm_OAI_TraceEnsemble_hasSum_expectation_basis

-- ---- from OAI.InformationTheory.PhotonNumber.SpectralLog ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace SquareAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I : Type*}

variable [CompleteSpace E]

end SquareAnalysis

namespace QuantumTrace
open scoped ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace Annihilation

namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n}

end GibbsData
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end SpectralLogData
end EntropyPhotonNumber

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

end

theorem trace_one_numberBasis {n : ℕ} (ρ : State n) :
    HasSum (fun k => (inner ℂ (numberBasis n k) (ρ.op (numberBasis n k))).re) 1 := by
  simpa only [numberBasis_apply, entry] using ρ.trace_one

end EntropyPhotonNumber

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber
open QuantumTrace TraceEnsemble

end EntropyPhotonNumber

namespace QuantumTrace

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I : Type*}

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace

end

open QuantumTrace Annihilation
variable {n : ℕ}

end EntropyPhotonNumber

end

end OAI

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

theorem block_eigen (M : Matrix I I ℂ) (hM : M.IsHermitian) (i : I) :
    block b M (basis b hM.eigenvectorBasis (Sum.inl i)) =
      (hM.eigenvalues i : ℂ) • basis b hM.eigenvectorBasis (Sum.inl i) := by
  rw [basis_inl, block_embed, hM.mulVec_eigenvectorBasis]
  simp only [WithLp.toLp_smul, WithLp.toLp_ofLp]
  change embed b ((hM.eigenvalues i : ℂ) • hM.eigenvectorBasis i) = _
  exact map_smul (embed b) _ _

end

open NormedSpace Matrix
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

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

theorem hasSum_expectation_basis {n : ℕ} {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (ρ : State n) (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun j => inner ℂ (b j) (Z (ρ.op (b j)))) (expectation ρ Z) := by
  simpa only [rootColumn_operator, expectation] using
    TraceEnsemble.hasSum_expectation_basis b (rootColumn_norm ρ).summable Z

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

omit [DecidableEq I] in
 theorem block_adjoint (b : HilbertBasis (I ⊕ J) ℂ E) (M : Matrix I I ℂ) :
    (block b M).adjoint = block b M.conjTranspose := by
  classical
  simp only [block, map_sum, map_smulₛₗ, InnerProductSpace.adjoint_rankOne]
  rw [Finset.sum_comm]
  rfl

omit [DecidableEq I] in
 theorem block_symmetric (b : HilbertBasis (I ⊕ J) ℂ E) (M : Matrix I I ℂ)
    (hM : M.IsHermitian) : (block b M).IsSymmetric := by
  rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, isSelfAdjoint_iff]
  change (block b M).adjoint = block b M
  rw [block_adjoint, hM.eq]

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

 theorem expectation_block_eigen (σ : State n) (b : HilbertBasis (I ⊕ J) ℂ (Fock n))
    (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    (expectation σ (FiniteBlock.block b M)).re = ∑ i, hM.eigenvalues i*
      (inner ℂ (FiniteBlock.basis b hM.eigenvectorBasis (Sum.inl i))
        (σ.op (FiniteBlock.basis b hM.eigenvectorBasis (Sum.inl i)))).re := by
  let a := FiniteBlock.basis b hM.eigenvectorBasis
  have hh := (hasSum_expectation_basis a σ (FiniteBlock.block b M)).mapL Complex.reCLM
  have he (j : I ⊕ J) :
      (inner ℂ (a j) (FiniteBlock.block b M (σ.op (a j)))).re =
        Sum.elim (fun i => hM.eigenvalues i*(inner ℂ (a (Sum.inl i)) (σ.op (a (Sum.inl i)))).re)
          (fun _ => 0) j := by
    erw [← FiniteBlock.block_symmetric b M hM (a j) (σ.op (a j))]
    cases j with
    | inl i =>
      change (inner ℂ (FiniteBlock.block b M (FiniteBlock.basis b hM.eigenvectorBasis (Sum.inl i))) (σ.op (a (Sum.inl i)))).re = _
      rw [FiniteBlock.block_eigen b M hM i, inner_smul_left]
      simp [a]
    | inr j => simp [a, FiniteBlock.block_tail]
  have hz : HasSum (Sum.elim
      (fun i => hM.eigenvalues i*(inner ℂ (a (Sum.inl i)) (σ.op (a (Sum.inl i)))).re)
      (fun _ : J => (0:ℝ)))
      (∑ i, hM.eigenvalues i*(inner ℂ (a (Sum.inl i)) (σ.op (a (Sum.inl i)))).re) := by
    simpa only [Function.comp_def, Sum.elim_inl, add_zero] using HasSum.sum (f := Sum.elim (fun i => hM.eigenvalues i*(inner ℂ (a (Sum.inl i)) (σ.op (a (Sum.inl i)))).re) (fun _ : J => (0:ℝ))) (hasSum_fintype _) (hasSum_zero : HasSum (fun _ : J => (0:ℝ)) 0)
  exact (by simpa only [Complex.reCLM_apply, he] using hh : HasSum _ _).unique hz

 theorem expectation_block_diagonal (σ : State n) (b : HilbertBasis (I ⊕ J) ℂ (Fock n))
    (d : I → ℝ) :
    (expectation σ (FiniteBlock.block b (Matrix.diagonal (fun i => (d i : ℂ))))).re =
      ∑ i, d i*(inner ℂ (b (Sum.inl i)) (σ.op (b (Sum.inl i)))).re := by
  have hs : (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := Matrix.isHermitian_diagonal_iff.mpr (by intro i; exact isSelfAdjoint_iff.mpr (Complex.conj_ofReal _))
  have he (j : I ⊕ J) :
      (inner ℂ (b j) (FiniteBlock.block b (Matrix.diagonal (fun i => (d i : ℂ))) (σ.op (b j)))).re =
        Sum.elim (fun i => d i*(inner ℂ (b (Sum.inl i)) (σ.op (b (Sum.inl i)))).re)
          (fun _ => 0) j := by
    erw [← FiniteBlock.block_symmetric b _ hs (b j) (σ.op (b j))]
    cases j with
    | inl i =>
      have hb : FiniteBlock.block b (Matrix.diagonal (fun i => (d i : ℂ))) (b (Sum.inl i)) =
          (d i : ℂ) • b (Sum.inl i) := by
        classical
        simp only [FiniteBlock.block, sum_apply, smul_apply,
          InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal]
        simp [Matrix.diagonal_apply]
      change (inner ℂ (FiniteBlock.block b (Matrix.diagonal (fun i => (d i : ℂ))) (b (Sum.inl i))) (σ.op (b (Sum.inl i)))).re = _
      rw [hb, inner_smul_left]
      simp
    | inr j => simp [FiniteBlock.block_tail]
  have hh := (hasSum_expectation_basis b σ (FiniteBlock.block b (Matrix.diagonal (fun i => (d i : ℂ))))).mapL Complex.reCLM
  have hz := HasSum.sum (f := Sum.elim (fun i => d i*(inner ℂ (b (Sum.inl i)) (σ.op (b (Sum.inl i)))).re) (fun _ : J => (0:ℝ))) (hasSum_fintype (fun i => d i*(inner ℂ (b (Sum.inl i)) (σ.op (b (Sum.inl i)))).re))
    (hasSum_zero : HasSum (fun _ : J => (0:ℝ)) 0)
  exact (by simpa only [Complex.reCLM_apply, he] using hh : HasSum _ _).unique
    (by simpa only [Function.comp_def, Sum.elim_inl, add_zero] using hz)

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

end FiniteBlock

namespace EntropyPhotonNumber

section
open QuantumTrace TraceEnsemble
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end

section
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

theorem block_crossEntropy (σ : State n) (b : HilbertBasis (I ⊕ J) ℂ (Fock n))
    (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (hc : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re))
    (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    HasSum (fun j => (-Real.log (FiniteBlock.weights p M hM j))*
      (inner ℂ (FiniteBlock.basis b hM.eigenvectorBasis j)
        (σ.op (FiniteBlock.basis b hM.eigenvectorBasis j))).re)
      (crossEntropy b p σ+
        (expectation σ (FiniteBlock.block b (Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ))))).re-
        (expectation σ (FiniteBlock.block b M)).re+Real.log (FiniteBlock.partition p M hM)) := by
  let a := FiniteBlock.basis b hM.eigenvectorBasis
  let C := ∑' j, (-Real.log (p (Sum.inr j)))*(inner ℂ (b (Sum.inr j)) (σ.op (b (Sum.inr j)))).re
  have ht : HasSum (fun j => (-Real.log (p (Sum.inr j)))*
      (inner ℂ (b (Sum.inr j)) (σ.op (b (Sum.inr j)))).re) C :=
    (hc.comp_injective Sum.inr_injective).hasSum
  have ho : HasSum (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re)
      ((∑ i, (-Real.log (p (Sum.inl i)))*(inner ℂ (b (Sum.inl i)) (σ.op (b (Sum.inl i)))).re)+C) :=
    HasSum.sum (hasSum_fintype _) ht
  have hC : C = crossEntropy b p σ+
      (expectation σ (FiniteBlock.block b (Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ))))).re := by
    have hh := ho.unique hc.hasSum
    rw [expectation_block_diagonal]
    dsimp only [crossEntropy]
    simp only [neg_mul, Finset.sum_neg_distrib] at hh ⊢
    linarith
  have h0 : HasSum (Sum.elim (fun _ : I => (0:ℝ))
      (fun j => (-Real.log (p (Sum.inr j)))*(inner ℂ (b (Sum.inr j)) (σ.op (b (Sum.inr j)))).re)) C := by
    simpa only [Function.comp_def, Sum.elim_inr, zero_add] using HasSum.sum (f := Sum.elim (fun _ : I => (0:ℝ)) (fun j => (-Real.log (p (Sum.inr j)))*(inner ℂ (b (Sum.inr j)) (σ.op (b (Sum.inr j)))).re)) (hasSum_zero : HasSum (fun _ : I => (0:ℝ)) 0) ht
  have h1 : HasSum (Sum.elim
      (fun i => hM.eigenvalues i*(inner ℂ (a (Sum.inl i)) (σ.op (a (Sum.inl i)))).re)
      (fun _ : J => (0:ℝ))) (expectation σ (FiniteBlock.block b M)).re := by
    rw [expectation_block_eigen]
    simpa only [Function.comp_def, Sum.elim_inl, add_zero] using HasSum.sum (f := Sum.elim (fun i => hM.eigenvalues i*(inner ℂ (a (Sum.inl i)) (σ.op (a (Sum.inl i)))).re) (fun _ : J => (0:ℝ))) (hasSum_fintype
      (fun i => hM.eigenvalues i*(inner ℂ (a (Sum.inl i)) (σ.op (a (Sum.inl i)))).re))
      (hasSum_zero : HasSum (fun _ : J => (0:ℝ)) 0)
  have h2 := (hasSum_trace_basis (numberBasis n) a σ.positive (trace_one_numberBasis σ)).mul_left
    (Real.log (FiniteBlock.partition p M hM))
  have hh := (h0.sub h1).add h2
  rw [mul_one, hC] at hh
  convert! hh using 1
  funext j
  cases j with
  | inl i =>
    simp only [FiniteBlock.weights, Sum.elim_inl,
      Real.log_div (Real.exp_pos _).ne' (FiniteBlock.partition_pos p hp hs M hM).ne', Real.log_exp]
    ring
  | inr j =>
    simp only [FiniteBlock.weights, Sum.elim_inr,
      Real.log_div (hp _).ne' (FiniteBlock.partition_pos p hp hs M hM).ne', a, FiniteBlock.basis_inr]
    ring

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
open QuantumTrace


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.block_crossEntropy := @_root_.OAI.EntropyPhotonNumber.block_crossEntropy
