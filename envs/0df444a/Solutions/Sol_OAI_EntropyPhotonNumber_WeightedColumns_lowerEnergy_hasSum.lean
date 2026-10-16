-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.WeightedColumns.lowerEnergy_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:37:34.154093+00:00
-- url     : https://prove2.me/submissions/f6383855-d905-405d-8493-e3dfb03c52c9

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Minimum.lean:L520-L542
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.WeightedColumns.lowerEnergy_hasSum. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Duality
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Minimum

-- ---- from OAI.InformationTheory.PhotonNumber.Minimum ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology _root_.Complex _root_.OAI.Complex Metric
open MeasureTheory Set Filter Topology _root_.Complex _root_.OAI.Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology _root_.Complex _root_.OAI.Complex MeasureTheory

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp BeamLadder
open scoped ComplexConjugate
variable {n : ℕ}

end

open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
variable {n : ℕ}
end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace TensorLp
variable {A B I J : Type*}
end TensorLp

namespace EntropyPhotonNumber.WeightedColumns
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {ρ σ τ : State n}

end EntropyPhotonNumber.WeightedColumns

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}
theorem weighted_lowering_norm_sum (j : Fin n) (x : Fock n) :
    HasSum (fun k : NumberIndex n => (k j:ℝ)*‖inverseWeight 3 x k‖^2)
      (‖sandwich 0 3 (by omega) j x‖^2) := by
  have hh := lowering_norm_sum j (inverseWeight 2 x)
  have hu : inverseWeight 1 (inverseWeight 2 x)=inverseWeight 3 x := by
    change (inverseWeight 1 ∘L inverseWeight 2) x=_
    rw [← inverseWeight_add]
  have hl : lowering j (inverseWeight 2 x)=sandwich 0 3 (by omega) j x := by
    exact congrArg (fun A : Fock n →L[ℂ] Fock n => A x) (sandwich_right_inverse 0 1 2 (by omega) j).symm
  simpa only [hu,hl] using hh
end Annihilation

namespace EntropyPhotonNumber.WeightedColumns

section
open QuantumTrace Annihilation
variable {n : ℕ} {ρ : State n}

theorem lowerEnergy_hasSum (X : WeightedColumns ρ) (j : Fin n) :
    HasSum (fun k => (k j:ℝ)*(entry ρ.op k k).re) (X.lowerEnergy j) := by
  let f := fun (i : X.Index) (k : NumberIndex n) => (k j:ℝ)*‖inverseWeight 3 (X.vector i) k‖^2
  have hrow (k : NumberIndex n) : HasSum (fun i => f i k) ((k j:ℝ)*(entry ρ.op k k).re) := by
    have hh := (TraceEnsemble.hasSum_quadratic X.normalized.summable (numberKet k)).mul_left (k j:ℝ)
    rw [show TraceEnsemble.operator (fun i => inverseWeight 3 (X.vector i))=ρ.op from X.density] at hh
    simpa only [f,numberKet,lp.inner_single_left,RCLike.inner_apply,map_one,one_mul,mul_one,entry] using hh
  have hcol i : HasSum (f i) (‖sandwich 0 3 (by omega) j (X.vector i)‖^2) :=
    weighted_lowering_norm_sum j (X.vector i)
  have hs : Summable (Function.uncurry f) := by
    apply (summable_prod_of_nonneg (fun ik => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).mpr
    refine ⟨fun i => (hcol i).summable,?_⟩
    convert CrossEnsemble.applied_summable X.summable (sandwich 0 3 (by omega) j) using 1
    ext i
    exact (hcol i).tsum_eq
  have hss : Summable (fun k => (k j:ℝ)*(entry ρ.op k k).re) := by
    exact hs.prod_symm.prod.congr (fun k => (hrow k).tsum_eq)
  have he : (∑' k, (k j:ℝ)*(entry ρ.op k k).re)=X.lowerEnergy j := by
    calc
      ∑' k, (k j:ℝ)*(entry ρ.op k k).re=∑' k, ∑' i, f i k := tsum_congr (fun k => (hrow k).tsum_eq.symm)
      _ = ∑' i, ∑' k, f i k := hs.tsum_comm
      _ = X.lowerEnergy j := tsum_congr (fun i => (hcol i).tsum_eq)
  simpa only [he] using hss.hasSum
end

section
open QuantumTrace Annihilation
variable {n : ℕ}

end

section
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ σ τ : State n}

end

open QuantumTrace
variable {n : ℕ}

end EntropyPhotonNumber.WeightedColumns

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace WeightedColumns
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

namespace EntropyPhotonNumber
open QuantumTrace WeightedColumns
variable {n : ℕ}

end EntropyPhotonNumber

end

namespace EntropyPhotonNumber
open scoped BigOperators ComplexConjugate

section
open TensorLp KrausBounded BeamLadder
variable {n : ℕ}

namespace Regularization
open QuantumTrace
variable (R : Regularization n)

end Regularization
end

open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

namespace GibbsData
variable {k : ℝ} (G : GibbsData n k ρ)
end GibbsData

end EntropyPhotonNumber

section
open scoped BigOperators

namespace WeightedGenerator

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}
end

end WeightedGenerator

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ}

end

open QuantumTrace Annihilation WeightedGenerator
variable {n : ℕ}

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber.Regularization
open QuantumTrace Annihilation
variable {n : ℕ} (R : Regularization n)

end EntropyPhotonNumber.Regularization

namespace EntropyPhotonNumber

section
open QuantumTrace ThermalMetric

namespace ThermalSetup
variable (P : ThermalSetup)
end ThermalSetup

namespace WeightedColumns
variable {n : ℕ} {ρ : State n}
end WeightedColumns
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end SpectralLogData
end

open QuantumTrace ThermalMetric Annihilation
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end SpectralLogData
namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)
end GibbsData
namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)

end ThermalSetup

namespace ThermalDual

end ThermalDual
namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)

end ThermalSetup
end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.WeightedColumns
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Metric
open MeasureTheory Set Filter Topology Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology MeasureTheory
open QuantumTrace Annihilation


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.WeightedColumns.lowerEnergy_hasSum := @_root_.OAI.EntropyPhotonNumber.WeightedColumns.lowerEnergy_hasSum
