-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.first_dual_conditional
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:17:27.905956+00:00
-- url     : https://prove2.me/submissions/4c6b6d8b-1f0e-4dd1-bebb-c428c95d7a19

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Duality.lean:L90-L104
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.first_dual_conditional. The node keeps its source
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

-- ---- from OAI.Analysis.TensorLp ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

namespace TensorLp
variable {A B : Type*}
end TensorLp

namespace TensorLp
variable {A B : Type*}

end TensorLp

namespace TensorLp
variable {A B : Type*}

theorem hasSum_slice_inner (x y : H (A × B)) :
    HasSum (fun b => inner ℂ (slice x b) (slice y b)) (inner ℂ x y) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) x y
  have hr (b : B) : HasSum (fun a => inner ℂ (x (a,b)) (y (a,b)))
      (inner ℂ (slice x b) (slice y b)) := lp.hasSum_inner (𝕜 := ℂ) (slice x b) (slice y b)
  have hc : HasSum (fun ba : B × A => inner ℂ (x (ba.2,ba.1)) (y (ba.2,ba.1)))
      (inner ℂ x y) := (Equiv.prodComm B A).hasSum_iff.mpr h
  exact hc.prod_fiberwise hr

end TensorLp

end

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.BeamTrace ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}
end Annihilation

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}
end BeamLadder

namespace EntropyPhotonNumber
end EntropyPhotonNumber

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

theorem conjugate_inner (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n)
    (x y : JointFock n) :
    inner ℂ x (conjugate η hη Z y)=inner ℂ (beamUnitary η hη x) (liftLeft Z (beamUnitary η hη y)) := by
  change inner ℂ x ((beamUnitary η hη).symm (liftLeft Z (beamUnitary η hη y)))=_
  rw [← (beamUnitary η hη).inner_map_map, (beamUnitary η hη).apply_symm_apply]

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

end BeamLadder

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap

namespace KrausBounded

section
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace E] [CompleteSpace H]

end

variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

end KrausBounded

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J : Type*}

end TensorLp

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

end

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

namespace EntropyPhotonNumber
variable {n : ℕ}
end EntropyPhotonNumber

namespace TensorLp
variable {A B I : Type*}
end TensorLp

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end CrossEnsemble

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace TensorLp
variable {A B I : Type*}

end TensorLp

namespace TraceEnsemble
open TensorLp
variable {A B I J : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber
open TensorLp
end EntropyPhotonNumber

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Continuity ----
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

namespace EntropyPhotonNumber
open TensorLp
end EntropyPhotonNumber

namespace BlockUnitary
variable {J : Type*} [Fintype J]

variable {S : Type*} {I : S → Type*} [∀ s, Fintype (I s)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end BlockUnitary

namespace TensorLp
variable {A B I : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp FischerBeam

end EntropyPhotonNumber

namespace TensorLp
variable {A B : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp

end EntropyPhotonNumber

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber
open TensorLp
end EntropyPhotonNumber

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J : Type*}
end TensorLp

namespace KrausBounded
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

end KrausBounded

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
end EnsembleL2

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J : Type*}

end TensorLp

namespace KrausBounded

section
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

end

open scoped BigOperators ComplexConjugate
variable {E H K I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

end KrausBounded

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J K E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end TensorLp

namespace KrausBounded
open scoped BigOperators ComplexConjugate
variable {E H F I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace E] [CompleteSpace H] [CompleteSpace F]

theorem dual_composite (V : I → E →L[ℂ] H) (U : J → H →L[ℂ] F)
    (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (hU : ∀ x, HasSum (fun j => ‖U j x‖^2) (‖x‖^2)) (Z : F →L[ℂ] F) :
    dual (composite V U) (composite_norm V U hV hU) Z=dual V hV (dual U hU Z) := by
  ext y
  apply ext_inner_left ℂ
  intro x
  have hh := dual_entry (composite V U) (composite_norm V U hV hU) Z x y
  exact (hh.prod_fiberwise (fun i => dual_entry U hU Z (V i x) (V i y))).unique
    (dual_entry V hV (dual U hU Z) x y)

theorem dual_reindex {K : Type*} (e : K ≃ I) (V : I → E →L[ℂ] H)
    (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (hW : ∀ x, HasSum (fun k => ‖V (e k) x‖^2) (‖x‖^2)) (Z : H →L[ℂ] H) :
    dual (fun k => V (e k)) hW Z=dual V hV Z := by
  ext y
  apply ext_inner_left ℂ
  intro x
  exact (dual_entry _ hW Z x y).unique (e.hasSum_iff.mpr (dual_entry V hV Z x y))
end KrausBounded

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate

end EntropyPhotonNumber

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Duality ----
namespace OAI

noncomputable section

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end EntropyPhotonNumber.SpectralLogData

section
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace TensorLp
open EntropyPhotonNumber
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp KrausBounded BeamLadder Annihilation
variable {n : ℕ}

theorem joint_dual_conjugate (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n) :
    dual (jointKraus η hη) (jointKraus_norm η hη) Z=conjugate η hη Z := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [conjugate_inner]
  exact (dual_entry _ _ Z x y).unique (by
    simpa only [jointKraus, ContinuousLinearMap.comp_apply, sliceCLM_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe, slice_liftLeft]
      using hasSum_slice_inner (beamUnitary η hη x) (liftLeft Z (beamUnitary η hη y)))

theorem first_dual_conditional (η : ℝ) (hη : η ∈ Set.Icc 0 1) (σ : State n)
    (Z : Fock n →L[ℂ] Fock n) :
    dual (firstKraus η hη σ) (firstKraus_norm η hη σ) Z=
      conditionalLeft (rootColumn σ) (rootColumn_norm σ) (conjugate η hη Z) := by
  let V := fun j => tensorRight (A:=NumberIndex n) (rootColumn σ j)
  let U := jointKraus (n:=n) η hη
  have hV := rightFamily_norm (rootColumn σ) (rootColumn_norm σ) (A:=NumberIndex n)
  have hU := jointKraus_norm (n:=n) η hη
  have hr := dual_reindex (Equiv.prodComm _ _) (composite V U) (composite_norm V U hV hU)
    (fun x => (Equiv.prodComm _ _).hasSum_iff.mpr (composite_norm V U hV hU x)) Z
  change dual (firstKraus η hη σ) _ Z=dual (composite V U) _ Z at hr
  rw [hr, dual_composite V U hV hU]
  change dual V hV (dual (jointKraus η hη) hU Z)=_
  rw [joint_dual_conjugate]
  rfl

namespace WeightedColumns
variable {ρ σ τ : State n}

end WeightedColumns
end EntropyPhotonNumber

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

end

open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology Complex MeasureTheory

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace ThermalDual

variable {I J : Type*} [Fintype I] [Fintype J]

end ThermalDual

namespace ThermalSpectral
open EntropyPhotonNumber ThermalMetric
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace ThermalDual

section
open EntropyPhotonNumber ThermalMetric ThermalSpectral
open scoped BigOperators
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Fintype K]

end

section
variable {I J : Type*} [Fintype I] [Fintype J]

end

open scoped ComplexConjugate

end ThermalDual

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open TensorLp KrausBounded BeamLadder Annihilation


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.first_dual_conditional := @_root_.OAI.EntropyPhotonNumber.first_dual_conditional
