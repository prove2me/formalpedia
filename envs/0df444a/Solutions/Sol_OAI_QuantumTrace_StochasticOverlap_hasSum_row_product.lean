-- Prove2me | solution 1 for OAI.QuantumTrace.StochasticOverlap.hasSum_row_product
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:02:18.565986+00:00
-- url     : https://prove2.me/submissions/711da13b-956e-4064-88e1-80b4d081f023

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean:L50-L64
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.StochasticOverlap.hasSum_row_product. The node keeps its source
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

-- ---- from OAI.InformationTheory.PhotonNumber.GibbsVariational ----
namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal

namespace QuantumTrace

section
open scoped BigOperators
open Filter Topology

namespace StochasticOverlap
variable {I J : Type*} (a : StochasticOverlap I J)

theorem hasSum_row_product (p : I → ℝ) {s : ℝ} (hp : HasSum p s) :
    HasSum (fun ij : I × J => a.value ij.1 ij.2 * p ij.1) s := by
  have hs : Summable (fun ij : I × J => a.value ij.1 ij.2 * p ij.1) := by
    apply Summable.of_norm
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
    constructor
    · intro i
      simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (a.nonneg i _)] using
        (a.row i).summable.mul_right |p i|
    · simp_rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (a.nonneg _ _),
        tsum_mul_right, (a.row _).tsum_eq, one_mul]
      exact hp.summable.norm
  convert hs.hasSum using 1
  rw [hs.tsum_prod]
  simp only [tsum_mul_right, (a.row _).tsum_eq, one_mul, hp.tsum_eq]

end StochasticOverlap
end

section
open scoped BigOperators
variable {I J : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end

variable {J : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

end EntropyPhotonNumber

namespace QuantumTrace
variable {n : ℕ} {J : Type*} [Nonempty J]

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace
end

section
open QuantumTrace TraceEnsemble

end

section
open QuantumTrace

end

section
open QuantumTrace TensorLp

namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end

section
open QuantumTrace
namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end

open QuantumTrace TraceEnsemble

namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)
end GibbsData

end EntropyPhotonNumber

namespace TensorLp
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.QuantumTrace OAI.QuantumTrace.StochasticOverlap
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped BigOperators
open Filter Topology


theorem solution : type_of% @_root_.OAI.QuantumTrace.StochasticOverlap.hasSum_row_product := @_root_.OAI.QuantumTrace.StochasticOverlap.hasSum_row_product
