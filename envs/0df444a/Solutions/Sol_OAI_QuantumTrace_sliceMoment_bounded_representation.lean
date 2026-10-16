-- Prove2me | solution 1 for OAI.QuantumTrace.sliceMoment_bounded_representation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:50:25.376976+00:00
-- url     : https://prove2.me/submissions/b73e97b1-29f9-48ee-8e89-02275757ea98

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean:L1702-L1722
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.sliceMoment_bounded_representation. The node keeps its source
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

theorem gram_positive (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) :
    (gram f hs C hC hb).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self _

theorem gram_quadratic (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) (x : E) :
    (inner ℂ x (gram f hs C hC hb x)).re = ∑' i, ‖f i x‖^2 := by
  exact ((continuousMap f hs C hC hb).apply_norm_sq_eq_inner_adjoint_right x).symm.trans
    (vector_norm_sq f hs x)

theorem exists_positive_representation (f : I → E →ₗ[ℂ] ℂ)
    (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) :
    ∃ B : E →L[ℂ] E, B.IsPositive ∧ ∀ x, (inner ℂ x (B x)).re = ∑' i, ‖f i x‖^2 :=
  ⟨gram f hs C hC hb, gram_positive f hs C hC hb, gram_quadratic f hs C hC hb⟩

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

-- ---- from OAI.InformationTheory.PhotonNumber.Entropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace Annihilation
open EntropyPhotonNumber QuantumTrace WeightedShift
open scoped ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped BigOperators
variable {n : ℕ} {I : Type*}

end WeightedGenerator

namespace WeightedShift
variable {I K : Type*}
end WeightedShift

namespace EntropyPhotonNumber
open QuantumTrace WeightedShift Annihilation
variable {n : ℕ}

end EntropyPhotonNumber

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section
open Filter Topology

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open ContinuousLinearMap Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end QuantumTrace

end

namespace EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

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

namespace TraceEnsemble
open Filter Topology
open scoped BigOperators
variable {I A E G : Type*}
variable [NormedAddCommGroup G] [CompleteSpace G]

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end TraceEnsemble

namespace TensorLp
variable {A B : Type*}

end TensorLp

namespace EntropyPhotonNumber

section
open Filter Topology TensorLp

end

open QuantumTrace TraceEnsemble
end EntropyPhotonNumber

namespace QuantumTrace
open scoped ENNReal

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace
end

open QuantumTrace Filter Topology

namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I J : Type*}

variable [CompleteSpace E]

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

omit [CompleteSpace E] in
theorem sliceCoordinates_square (b : HilbertBasis J ℂ E) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (V : I → E →L[ℂ] E) (S : E →L[ℂ] E) (ij : I × J) (x : E) :
    ‖sliceCoordinates b w V S ij x‖^2 = w ij.2*‖inner ℂ (b ij.2) (V ij.1 (S x))‖^2 := by
  change ‖(Real.sqrt (w ij.2) : ℂ)*inner ℂ (b ij.2) (V ij.1 (S x))‖^2 = _
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hw _)]

omit [CompleteSpace E] in
theorem sliceCoordinates_sum (b : HilbertBasis J ℂ E) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (V : I → E →L[ℂ] E) (S : E →L[ℂ] E) (x : E) :
    (∑' ij, ENNReal.ofReal (‖sliceCoordinates b w V S ij x‖^2)) =
      sliceMoment b (fun j => ENNReal.ofReal (w j)) V (S x) := by
  simp only [sliceCoordinates_square b w hw, ENNReal.ofReal_mul (hw _),
    ENNReal.tsum_prod', sliceMoment, basisMoment]

theorem sliceMoment_bounded_representation (b : HilbertBasis J ℂ E) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (V : I → E →L[ℂ] E) (S : E →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, sliceMoment b (fun j => ENNReal.ofReal (w j)) V (S x) ≤
      ENNReal.ofReal (C*‖x‖^2)) :
    ∃ B : E →L[ℂ] E, B.IsPositive ∧ ∀ x,
      ENNReal.ofReal (inner ℂ x (B x)).re =
        sliceMoment b (fun j => ENNReal.ofReal (w j)) V (S x) := by
  let f := sliceCoordinates b w V S
  have hs (x : E) : Summable (fun ij => ‖f ij x‖^2) := by
    have hfinite : (∑' ij, ENNReal.ofReal (‖f ij x‖^2)) ≠ ⊤ := by
      rw [sliceCoordinates_sum b w hw]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb x)
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hfinite
  have hbound (x : E) : (∑' ij, ‖f ij x‖^2) ≤ C*‖x‖^2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (sq_nonneg _))).mp
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hs x), sliceCoordinates_sum b w hw]
    exact hb x
  obtain ⟨B,hB,he⟩ := SquareAnalysis.exists_positive_representation f hs hC hbound
  refine ⟨B,hB,fun x => ?_⟩
  rw [he, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hs x)]
  exact sliceCoordinates_sum b w hw V S x

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace TensorLp

end

open QuantumTrace

end EntropyPhotonNumber

namespace QuantumTrace

section
variable {ι J L : Type*}

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace TensorLp

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {J : Type*}

end QuantumTrace

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber
open QuantumTrace TraceEnsemble

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.QuantumTrace
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.QuantumTrace.sliceMoment_bounded_representation := @_root_.OAI.QuantumTrace.sliceMoment_bounded_representation
