-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.spectral_weighted_columns
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:27:36.153002+00:00
-- url     : https://prove2.me/submissions/a37db2c9-c231-41a1-864a-c1fc9e1fa0f5

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/SpectralLog.lean:L339-L360
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.spectral_weighted_columns. The node keeps its source
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

theorem spectral_weighted_columns (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ j, 0≤p j) (he : ∀ j, ρ.op (b j)=(p j:ℂ) • b j)
    (hm : FiniteMoment 6 ρ) :
    ∃ x : J → Fock n, Summable (fun j => ‖x j‖^2) ∧
      ∀ j, inverseWeight 3 (x j)=CrossEnsemble.eigenEnsemble b p j := by
  have hm' : Summable (fun i => (numberWeight i^3)^2*
      (inner ℂ (sequenceBasis (NumberIndex n) i) (ρ.op (sequenceBasis _ i))).re) := by
    have hb (i : NumberIndex n) : sequenceBasis (NumberIndex n) i = numberKet i := by
      ext a
      by_cases ha : i=a <;> simp [sequenceBasis_apply, numberKet, ha]
    simpa only [← pow_mul, show (3*2:ℕ)=6 from rfl, numberWeight, totalNumber, Nat.cast_sum,
      FiniteMoment, entry, hb] using hm
  obtain ⟨x, hx, hs, _⟩ := weighted_spectral_vectors b ρ.op p hp he
    (fun i => numberWeight i^3) hm'
  refine ⟨x, hs, fun j => ?_⟩
  apply lp.ext
  funext i
  simp only [inverseWeight_apply, hx, CrossEnsemble.eigenEnsemble, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, Complex.ofReal_pow]
  have hw : (numberWeight i : ℂ) ≠ 0 := by
    exact_mod_cast (show numberWeight i ≠ 0 by linarith [numberWeight_one_le i])
  field_simp

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

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber
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
open QuantumTrace Annihilation


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.spectral_weighted_columns := @_root_.OAI.EntropyPhotonNumber.spectral_weighted_columns
