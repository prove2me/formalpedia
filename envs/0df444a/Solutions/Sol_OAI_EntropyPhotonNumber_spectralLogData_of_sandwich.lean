-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.spectralLogData_of_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:41:16.286165+00:00
-- url     : https://prove2.me/submissions/0781cf86-2e52-441c-bc94-db5c93cbd090

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Minimum.lean:L783-L848
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.spectralLogData_of_sandwich. The node keeps its source
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
import Theorems.Thm_OAI_EntropyPhotonNumber_spectral_weighted_columns
import Theorems.Thm_OAI_QuantumTrace_positive_eq_of_quadratic
import Theorems.Thm_OAI_QuantumTrace_spectral_form_representation

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

theorem basisMoment_ofReal (b : HilbertBasis I ℂ E) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : E) (hs : Summable (fun i => w i*‖inner ℂ (b i) x‖^2)) :
    basisMoment b (fun i => ENNReal.ofReal (w i)) x =
      ENNReal.ofReal (∑' i, w i*‖inner ℂ (b i) x‖^2) := by
  simp only [basisMoment, ← ENNReal.ofReal_mul (hw _)]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hw i) (sq_nonneg _)) hs).symm

variable [CompleteSpace E]

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

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
end Annihilation

namespace EntropyPhotonNumber.WeightedColumns

section
open QuantumTrace Annihilation
variable {n : ℕ} {ρ : State n}

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

theorem spectralLogData_of_sandwich (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j)=(p j:ℂ) • b j) (hm : FiniteMoment 6 ρ)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive)
    (hBe : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re =
      basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x)) :
    ∃ G : SpectralLogData n ρ, G.J=J ∧ HEq G.basis b ∧ HEq G.probability p ∧ G.logSandwich=B := by
  have hc (j : J) : 0≤-Real.log (p j) := by
    apply neg_nonneg.mpr
    exact Real.log_nonpos (hp j).le (hs.tsum_eq ▸ hs.summable.le_tsum j (fun i _ => (hp i).le))
  have hfin (x : Fock n) : Summable (fun j => -Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 x)‖^2) := by
    have heq : (∑' j, ENNReal.ofReal (-Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 x)‖^2))=
        ENNReal.ofReal (inner ℂ x (B x)).re := by
      rw [hBe]; simp only [basisMoment, ENNReal.ofReal_mul (hc _)]
    have hfinite : (∑' j, ENNReal.ofReal (-Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 x)‖^2))≠⊤ :=
      heq ▸ ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal (mul_nonneg (hc _) (sq_nonneg _))] using ENNReal.summable_toReal hfinite
  have hsum (x : Fock n) : HasSum
      (fun j => -Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 x)‖^2) (inner ℂ x (B x)).re := by
    have hh := hBe x
    rw [basisMoment_ofReal b _ hc _ (hfin x)] at hh
    have hn : 0≤(inner ℂ x (B x)).re := hB.re_inner_nonneg_right x
    have hnn : 0≤∑' j, -Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 x)‖^2 :=
      tsum_nonneg (fun j => mul_nonneg (hc j) (sq_nonneg _))
    have heq : (inner ℂ x (B x)).re=∑' j, -Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 x)‖^2 :=
      by simpa only [ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal hnn] using congrArg ENNReal.toReal hh
    rw [heq]; exact (hfin x).hasSum
  have hb (x : Fock n) : (∑' j, -Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 x)‖^2) ≤ ‖B‖*‖x‖^2 := by
    rw [(hsum x).tsum_eq]
    calc
      (inner ℂ x (B x)).re ≤ ‖inner ℂ x (B x)‖ := Complex.re_le_norm _
      _ ≤ ‖x‖*‖B x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖*(‖B‖*‖x‖) := mul_le_mul_of_nonneg_left (B.le_opNorm x) (norm_nonneg _)
      _ = ‖B‖*‖x‖^2 := by ring
  obtain ⟨B',hB',hs',he'⟩ := spectral_form_representation b (fun j => -Real.log (p j)) hc
    (inverseWeight 2) (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (inverseWeight_selfAdjoint 2))
    hfin (norm_nonneg B) hb
  have hBB : B'=B := positive_eq_of_quadratic hB' hB (fun x => (hs' x).unique (hsum x))
  subst B'
  obtain ⟨x,hx,hix⟩ := spectral_weighted_columns b p (fun j => (hp j).le) he hm
  let G : SpectralLogData n ρ := {
    J := J
    basis := b
    probability := p
    probability_pos := hp
    probability_sum := hs
    eigen := he
    spectralColumns := x
    spectralColumns_summable := hx
    spectralColumns_inverse := hix
    logSandwich := B
    logSandwich_symmetric := hB.isSymmetric
    logSandwich_parseval := hsum
    logSandwich_preimage := by
      intro j
      have hi : inverseWeight 2 (inverseWeight 1 (x j))=(Real.sqrt (p j):ℂ) • b j := by
        change (inverseWeight 2 ∘L inverseWeight 1) (x j)=_
        rw [← inverseWeight_add]
        exact hix j
      have hh := he' j (inverseWeight 1 (x j)) (Real.sqrt (p j):ℂ) hi
      have hz : inverseWeight 2 ((Real.sqrt (p j):ℂ) • b j)=inverseWeight 5 (x j) := by
        rw [← hi]
        change (inverseWeight 2 ∘L inverseWeight 2 ∘L inverseWeight 1) (x j)=_
        rw [← inverseWeight_add,← inverseWeight_add]
      simpa only [hz] using hh }
  exact ⟨G,rfl,HEq.rfl,HEq.rfl,rfl⟩

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
open OAI OAI.EntropyPhotonNumber
open scoped BigOperators ComplexConjugate
open QuantumTrace Annihilation


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.spectralLogData_of_sandwich := @_root_.OAI.EntropyPhotonNumber.spectralLogData_of_sandwich
