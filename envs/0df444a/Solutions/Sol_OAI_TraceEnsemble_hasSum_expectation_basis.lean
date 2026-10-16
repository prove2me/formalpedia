-- Prove2me | solution 1 for OAI.TraceEnsemble.hasSum_expectation_basis
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:49:10.398749+00:00
-- url     : https://prove2.me/submissions/515e47ae-34d7-4201-a64e-3cb6cfab1928

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean:L341-L358
-- (upload_full_project.md Phase 4): solution for node OAI.TraceEnsemble.hasSum_expectation_basis. The node keeps its source
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

variable [DecidableEq I]

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

omit [CompleteSpace E] in
theorem summable_basis_square (b : HilbertBasis J ℂ E) {v : I → E}
    (hv : Summable (fun i => ‖v i‖^2)) :
    Summable (fun ij : I × J => ‖inner ℂ (b ij.2) (v ij.1)‖^2) := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  exact ⟨fun i => (basis_hasSum_norm_sq b (v i)).summable,
    by simpa only [(basis_hasSum_norm_sq b _).tsum_eq] using hv⟩

omit [CompleteSpace E] in
theorem summable_map_square {v : I → E} (hv : Summable (fun i => ‖v i‖^2))
    (Z : E →L[ℂ] E) : Summable (fun i => ‖Z (v i)‖^2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hv.mul_left (‖Z‖^2))
  intro i
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (Z.le_opNorm (v i)) 2

omit [CompleteSpace E] in
theorem summable_trace_pair (b : HilbertBasis J ℂ E) {v : I → E}
    (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    Summable (fun ij : I × J => inner ℂ (v ij.1) (b ij.2)*inner ℂ (b ij.2) (Z (v ij.1))) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (((summable_basis_square b hv).add
      (summable_basis_square b (summable_map_square hv Z))).div_const 2)
  intro ij
  simp only [norm_mul, norm_inner_symm (v ij.1) (b ij.2)]
  nlinarith [sq_nonneg (‖inner ℂ (b ij.2) (v ij.1)‖-‖inner ℂ (b ij.2) (Z (v ij.1))‖)]

theorem hasSum_expectation_basis (b : HilbertBasis J ℂ E) {v : I → E}
    (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    HasSum (fun j => inner ℂ (b j) (Z (operator v (b j)))) (expectation v Z) := by
  have hd := summable_trace_pair b hv Z
  have hrow (i : I) : HasSum (fun j => inner ℂ (v i) (b j)*inner ℂ (b j) (Z (v i)))
      (inner ℂ (v i) (Z (v i))) := b.hasSum_inner_mul_inner (v i) (Z (v i))
  have hcol (j : J) : HasSum (fun i => inner ℂ (v i) (b j)*inner ℂ (b j) (Z (v i)))
      (inner ℂ (b j) (Z (operator v (b j)))) := by
    have hh := (((ContinuousLinearMap.apply ℂ E (b j)).hasSum (hasSum_rankOne hv)).mapL Z).mapL
      (innerSL ℂ (b j))
    simpa only [ContinuousLinearMap.apply_apply, InnerProductSpace.rankOne_apply,
      map_smul, innerSL_apply_apply, inner_smul_right, smul_eq_mul] using hh
  have he : (∑' ij : I × J, inner ℂ (v ij.1) (b ij.2)*inner ℂ (b ij.2) (Z (v ij.1))) =
      expectation v Z := by
    rw [hd.tsum_prod]
    simp only [(hrow _).tsum_eq, expectation]
  rw [← he]
  exact ((Equiv.prodComm J I).hasSum_iff.2 hd.hasSum).prod_fiberwise hcol

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

end FiniteBlock

namespace EntropyPhotonNumber

section
open QuantumTrace TraceEnsemble
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

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
open OAI OAI.TraceEnsemble
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


theorem solution : type_of% @_root_.OAI.TraceEnsemble.hasSum_expectation_basis := @_root_.OAI.TraceEnsemble.hasSum_expectation_basis
