-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.Regularization.minimum_spectral_pairing_balance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:45:45.59811+00:00
-- url     : https://prove2.me/submissions/d2e5208b-1c7d-49a4-8d64-0fa7d8dc0e02

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Minimum.lean:L1131-L1199
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.Regularization.minimum_spectral_pairing_balance. The node keeps its source
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
import Theorems.Thm_OAI_EntropyPhotonNumber_Regularization_canonical_output_generator
import Theorems.Thm_OAI_EntropyPhotonNumber_Regularization_minimum_physical_pairing_balance
import Theorems.Thm_OAI_EntropyPhotonNumber_first_dual_conditional
import Theorems.Thm_OAI_EntropyPhotonNumber_spectralLogData_of_sandwich
import Theorems.Thm_OAI_QuantumTrace_positive_eq_of_quadratic

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

theorem diagonal_quadratic (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k| ≤ C) (x : Fock n) :
    HasSum (fun k => f k*‖x k‖^2) (inner ℂ x (diagonal f C hC hf x)).re := by
  have hh := (lp.hasSum_inner (𝕜 := ℂ) x (diagonal f C hC hf x)).mapL Complex.reCLM
  convert! hh using 1
  ext k
  simp only [RCLike.inner_apply, diagonal_apply, Complex.reCLM_apply]
  rw [mul_assoc, Complex.mul_conj, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.normSq_eq_norm_sq]

theorem diagonal_selfAdjoint (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k| ≤ C) : IsSelfAdjoint (diagonal f C hC hf) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  apply HasSum.unique (lp.hasSum_inner (𝕜 := ℂ) (diagonal f C hC hf x) y)
  convert! lp.hasSum_inner (𝕜 := ℂ) x (diagonal f C hC hf y) using 1
  ext k
  simp only [diagonal_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

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

theorem numberVectorMoment_eq {n : ℕ} (x : Fock n) :
    numberVectorMoment x = ∑' k, ENNReal.ofReal ((totalNumber k : ℝ)*‖inner ℂ (numberBasis n k) x‖^2) := by
  simp only [numberVectorMoment, basisMoment, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

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

-- ---- from OAI.InformationTheory.PhotonNumber.PhysicalMinimum ----
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
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open Filter Asymptotics Topology
open ContinuousLinearMap

namespace TensorLp
open scoped ENNReal
variable {A B : Type*}

end TensorLp

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {J : Type*}

end BeamLadder

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ}
namespace GibbsData
variable {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end GibbsData

theorem weightedRoot_inverse_one (ρ : State n) (hm : FiniteMoment 6 ρ)
    (hm4 : FiniteMoment 4 ρ) (i : NumberIndex n) :
    inverseWeight 1 (weightedRoot 3 ρ hm i)=weightedRoot 2 ρ hm4 i := by
  apply lp.ext
  funext k
  have hw : (numberWeight k:ℂ) ≠ 0 := by
    exact_mod_cast (show numberWeight k ≠ 0 by linarith [numberWeight_one_le k])
  simp only [inverseWeight_apply,weightedRoot_apply,Complex.ofReal_pow,pow_one]
  field_simp

namespace WeightedColumns

theorem canonical_slice (ρ : State n) (hm : FiniteMoment 6 ρ) (hm4 : FiniteMoment 4 ρ)
    (η : ℝ) (hη : η ∈ Set.Icc 0 1) (B : Fock n →L[ℂ] Fock n) :
    (canonical ρ hm).slice η hη B=weightedConditional η hη (weightedRoot 2 ρ hm4) B := by
  unfold slice canonical
  congr 1
  funext i
  exact weightedRoot_inverse_one ρ hm hm4 i

theorem canonical_sliceRight (ρ : State n) (hm : FiniteMoment 6 ρ) (hm4 : FiniteMoment 4 ρ)
    (η : ℝ) (hη : η ∈ Set.Icc 0 1) (B : Fock n →L[ℂ] Fock n) :
    (canonical ρ hm).sliceRight η hη B=weightedConditionalRight η hη (weightedRoot 2 ρ hm4) B := by
  unfold sliceRight canonical
  congr 1
  funext i
  exact weightedRoot_inverse_one ρ hm hm4 i
end WeightedColumns

end

section
open QuantumTrace TensorLp

end

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)

end GibbsData
end

namespace Regularization
open QuantumTrace
variable {n : ℕ} (R : Regularization n)

end Regularization

open QuantumTrace Annihilation BeamLadder TensorLp
namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ} {I : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)
end GibbsData
end

namespace Regularization

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} (R : Regularization n)

end

open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} (R : Regularization n)

end Regularization

open QuantumTrace Annihilation BeamLadder TensorLp

namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
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

theorem second_dual_conditional (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρ : State n)
    (Z : Fock n →L[ℂ] Fock n) :
    dual (secondKraus η hη ρ) (secondKraus_norm η hη ρ) Z=
      conditionalRight (rootColumn ρ) (rootColumn_norm ρ) (conjugate η hη Z) := by
  let V := fun j => tensorLeft (B:=NumberIndex n) (rootColumn ρ j)
  let U := jointKraus (n:=n) η hη
  have hV := leftFamily_norm (rootColumn ρ) (rootColumn_norm ρ) (B:=NumberIndex n)
  have hU := jointKraus_norm (n:=n) η hη
  have hr := dual_reindex (Equiv.prodComm _ _) (composite V U) (composite_norm V U hV hU)
    (fun x => (Equiv.prodComm _ _).hasSum_iff.mpr (composite_norm V U hV hU x)) Z
  change dual (secondKraus η hη ρ) _ Z=dual (composite V U) _ Z at hr
  rw [hr, dual_composite V U hV hU]
  change dual V hV (dual (jointKraus η hη) hU Z)=_
  rw [joint_dual_conjugate]
  rfl

theorem dual_composeKraus {I J : Type*} (U : I → Fock n →L[ℂ] Fock n)
    (V : J → Fock n →L[ℂ] Fock n)
    (hU : ∀ x, HasSum (fun i => ‖U i x‖^2) (‖x‖^2))
    (hV : ∀ x, HasSum (fun j => ‖V j x‖^2) (‖x‖^2)) (Z : Fock n →L[ℂ] Fock n) :
    dual (composeKraus U V) (composeKraus_norm U V hU hV) Z=dual V hV (dual U hU Z) := by
  have hr := dual_reindex (Equiv.prodComm _ _) (composite V U) (composite_norm V U hV hU)
    (fun x => (Equiv.prodComm _ _).hasSum_iff.mpr (composite_norm V U hV hU x)) Z
  change dual (composeKraus U V) _ Z=dual (composite V U) _ Z at hr
  rw [hr,dual_composite V U hV hU]

namespace Regularization
open QuantumTrace
variable (R : Regularization n)

theorem firstFlow_dual_raw (σ : State n) (hσ : FiniteEnergy σ) (Z : Fock n →L[ℂ] Fock n) :
    (R.firstFlow σ hσ).dual Z=rawFirstSlice R.η (1-R.δ) R.hη
      ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩ σ R.τD Z := by
  have hθ : 1-R.δ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
  change dual (composeKraus (firstKraus (1-R.δ) hθ R.τD) (firstKraus R.η R.hη σ))
    (composeKraus_norm _ _ (firstKraus_norm _ _ _) (firstKraus_norm _ _ _)) Z=
    rawFirstSlice R.η (1-R.δ) R.hη hθ σ R.τD Z
  rw [dual_composeKraus _ _ (firstKraus_norm _ _ _) (firstKraus_norm _ _ _), first_dual_conditional]
  unfold rawFirstSlice rawDual rawJointKraus
  have hd := dual_composite (jointKraus R.η R.hη)
    (firstKraus (1-R.δ) (show 1-R.δ ∈ Set.Icc 0 1 from ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩) R.τD)
    (jointKraus_norm R.η R.hη) (firstKraus_norm _ _ _) Z
  rw [joint_dual_conjugate] at hd
  exact congrArg (conditionalLeft (rootColumn σ) (rootColumn_norm σ)) hd.symm

theorem secondFlow_dual_raw (ρ : State n) (hρ : FiniteEnergy ρ) (Z : Fock n →L[ℂ] Fock n) :
    (R.secondFlow ρ hρ).dual Z=rawSecondSlice R.η (1-R.δ) R.hη
      ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩ ρ R.τD Z := by
  have hθ : 1-R.δ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
  change dual (composeKraus (firstKraus (1-R.δ) hθ R.τD) (secondKraus R.η R.hη ρ))
    (composeKraus_norm _ _ (firstKraus_norm _ _ _) (secondKraus_norm _ _ _)) Z=
    rawSecondSlice R.η (1-R.δ) R.hη hθ ρ R.τD Z
  rw [dual_composeKraus _ _ (firstKraus_norm _ _ _) (secondKraus_norm _ _ _), second_dual_conditional]
  unfold rawSecondSlice rawDual rawJointKraus
  have hd := dual_composite (jointKraus R.η R.hη)
    (firstKraus (1-R.δ) (show 1-R.δ ∈ Set.Icc 0 1 from ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩) R.τD)
    (jointKraus_norm R.η R.hη) (firstKraus_norm _ _ _) Z
  rw [joint_dual_conjugate] at hd
  exact congrArg (conditionalRight (rootColumn ρ) (rootColumn_norm ρ)) hd.symm
end Regularization
end

open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

namespace GibbsData
variable {k : ℝ} (G : GibbsData n k ρ)
theorem quarticLogarithm_eq_logSandwich : G.quarticLogarithm=G.logSandwich := by
  unfold quarticLogarithm logSandwich
  rw [inversePower_root_four]
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

theorem numberSandwich_positive (n : ℕ) : (numberSandwich n).IsPositive := by
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (diagonal_selfAdjoint _ _ _ _), ?_⟩
  intro x
  have hh := diagonal_quadratic (fun k : NumberIndex n => (totalNumber k:ℝ)/numberWeight k^4) 1 (by norm_num) number_div_weight_bound x
  have hs : (inner ℂ x (numberSandwich n x)).re=∑' k, (totalNumber k:ℝ)/numberWeight k^4*‖x k‖^2 := hh.tsum_eq.symm
  change 0≤(inner ℂ (numberSandwich n x) x).re
  rw [show (inner ℂ (numberSandwich n x) x).re=(inner ℂ x (numberSandwich n x)).re from inner_re_symm (𝕜:=ℂ) _ _, hs]
  exact tsum_nonneg (fun k => by positivity)

theorem numberSandwich_form (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (numberSandwich n x)).re = numberVectorMoment (inverseWeight 2 x) := by
  rw [numberVectorMoment_eq]
  have hh := diagonal_quadratic (fun k : NumberIndex n => (totalNumber k:ℝ)/numberWeight k^4) 1 (by norm_num) number_div_weight_bound x
  change HasSum _ (inner ℂ x (numberSandwich n x)).re at hh
  rw [← hh.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hh.summable]
  apply tsum_congr
  intro k
  congr 1
  simp [numberBasis_apply,numberKet,lp.inner_single_left,inverseWeight_apply,
    norm_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (le_trans zero_le_one (numberWeight_one_le k))]
  ring

theorem numberSandwich_unique (D : Fock n →L[ℂ] Fock n) (hD : D.IsPositive)
    (he : ∀ x, ENNReal.ofReal (inner ℂ x (D x)).re =
      numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) :
    D=numberSandwich n := by
  apply positive_eq_of_quadratic hD (numberSandwich_positive n)
  intro x
  have hh := congrArg ENNReal.toReal (he x)
  rw [inversePower_root_four, ← numberSandwich_form] at hh
  simpa only [ENNReal.toReal_ofReal (show 0≤(inner ℂ x (D x)).re from hD.re_inner_nonneg_right x),
    ENNReal.toReal_ofReal (show 0≤(inner ℂ x (numberSandwich n x)).re from (numberSandwich_positive n).re_inner_nonneg_right x)] using hh

end

open QuantumTrace Annihilation WeightedGenerator
variable {n : ℕ}

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber.Regularization
open QuantumTrace Annihilation
variable {n : ℕ} (R : Regularization n)

theorem thermal_state_diagonal (r : ℝ) (hr : 0<r) (k l : NumberIndex n) :
    entry (thermalState n r hr).op k l=if k=l then (thermalWeight n r k:ℂ) else 0 := by
  rw [entry,← numberBasis_apply n k,← numberBasis_apply n l]
  change inner ℂ (numberBasis n k) ((diagonalState _ _ _).op (numberBasis n l))=_
  rw [diagonalState_eigen,inner_smul_right,
    orthonormal_iff_ite.mp (numberBasis n).orthonormal k l]
  split_ifs with h
  · subst l; simp only [mul_one]
  · simp only [mul_zero]

theorem minimum_spectral_pairing_balance (ρ σ : State n)
    (hmρ : FiniteMoment 4 ρ) (hmσ : FiniteMoment 4 σ)
    (s1 s2 d r0 : ℝ) (hd : 0<d) (hr0 : 0<r0)
    (heq : r0=(1-R.δ)*(R.η*s1+(1-R.η)*s2)+(1-(1-R.δ))*d)
    (hD : R.τD=thermalState n d hd) (hτ : R.τ0=thermalState n r0 hr0)
    (hκ : 0<R.κ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' → R.objective ρ σ ≤ R.objective ρ' σ') :
    ∃ (G1 : GibbsData n (R.ζ/R.a1) ρ) (G2 : GibbsData n (R.ζ/R.a2) σ)
      (G0 : SpectralLogData n (R.output ρ σ))
      (h6ρ : FiniteMoment 6 ρ) (h6σ : FiniteMoment 6 σ) (h60 : FiniteMoment 6 (R.output ρ σ)),
      (R.a1:ℂ)*WeightedGenerator.pairing s1 (weightedRoot 3 ρ h6ρ) G1.logSandwich+
      (R.a2:ℂ)*WeightedGenerator.pairing s2 (weightedRoot 3 σ h6σ) G2.logSandwich=
      (R.c:ℂ)*WeightedGenerator.pairing r0 (weightedRoot 3 (R.output ρ σ) h60) G0.logSandwich+
      (R.b1:ℂ)*WeightedGenerator.pairing s1 (weightedRoot 3 ρ h6ρ) (numberSandwich n)+
      (R.b2:ℂ)*WeightedGenerator.pairing s2 (weightedRoot 3 σ h6σ) (numberSandwich n)+
      (R.ζ:ℂ)*(WeightedGenerator.pairing s1 (weightedRoot 3 ρ h6ρ) (1 : Fock n →L[ℂ] Fock n)+
        WeightedGenerator.pairing s2 (weightedRoot 3 σ h6σ) (1 : Fock n →L[ℂ] Fock n)) ∧
      (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
        (1-R.κ)^2*BKM.quadratic G1.basis G1.probability
          (BKM.center G1.basis G1.probability
            (rawFirstSlice R.η (1-R.δ) R.hη R.attenuation_mem σ R.τD Z)) ≤
          (R.a1/R.c)*BKM.quadratic G0.basis G0.probability Z) ∧
      (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
        (1-R.κ)^2*BKM.quadratic G2.basis G2.probability
          (BKM.center G2.basis G2.probability
            (rawSecondSlice R.η (1-R.δ) R.hη R.attenuation_mem ρ R.τD Z)) ≤
          (R.a2/R.c)*BKM.quadratic G0.basis G0.probability Z) := by
  have h6D : FiniteMoment 6 R.τD := by rw [hD]; exact thermalState_finiteMoment n 6 d hd
  have h4D : FiniteMoment 4 R.τD := finiteMoment_mono (by norm_num) h6D
  have h6O : FiniteMoment 6 R.τ0 := by rw [hτ]; exact thermalState_finiteMoment n 6 r0 hr0
  obtain ⟨J,b,p,hp,hs,he,G1,G2,B,D1,D2,hB,hD1,hD2,hBe,heD1,heD2,hbal,hh1,hh2⟩ :=
    R.minimum_physical_pairing_balance ρ σ hmρ hmσ h4D hr0 hτ hκ hmin
  have h6ρ : FiniteMoment 6 ρ := finiteMoment_mono (by norm_num) G1.moment
  have h6σ : FiniteMoment 6 σ := finiteMoment_mono (by norm_num) G2.moment
  obtain ⟨h60,hcov⟩ := R.canonical_output_generator ρ σ h6ρ h6σ h6D h6O
    s1 s2 d r0 hd hr0 heq
    (by intro k l; rw [hD]; exact thermal_state_diagonal d hd k l)
    (by intro k l; rw [hτ]; exact thermal_state_diagonal r0 hr0 k l) B
  have hb := hbal s1 s2 (WeightedColumns.canonical ρ h6ρ) (WeightedColumns.canonical σ h6σ)
  have hθ : 1-R.δ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
  change WeightedGenerator.pairing r0 (WeightedColumns.canonical (R.output ρ σ) h60).vector B=
    ((1-R.κ:ℝ):ℂ)*(WeightedGenerator.pairing s1 (WeightedColumns.canonical ρ h6ρ).vector
      ((WeightedColumns.canonical σ h6σ).slice R.η R.hη
        ((WeightedColumns.canonical R.τD h6D).slice (1-R.δ) hθ B))+
      WeightedGenerator.pairing s2 (WeightedColumns.canonical σ h6σ).vector
      ((WeightedColumns.canonical ρ h6ρ).sliceRight R.η R.hη
        ((WeightedColumns.canonical R.τD h6D).slice (1-R.δ) hθ B))) at hcov
  rw [WeightedColumns.canonical_slice R.τD h6D h4D,
    WeightedColumns.canonical_slice σ h6σ hmσ,
    WeightedColumns.canonical_sliceRight ρ h6ρ hmρ] at hcov
  rw [mul_assoc (R.c:ℂ),← hcov] at hb
  rw [G1.quarticLogarithm_eq_logSandwich,G2.quarticLogarithm_eq_logSandwich,
    numberSandwich_unique D1 hD1 heD1,numberSandwich_unique D2 hD2 heD2] at hb
  obtain ⟨G0,hJ,hbasis,hprob,hlog⟩ := spectralLogData_of_sandwich b p hp hs he h60 B hB hBe
  cases hJ
  have hbEq := eq_of_heq hbasis
  have hpEq := eq_of_heq hprob
  subst b
  subst p
  refine ⟨G1,G2,G0,h6ρ,h6σ,h60,?_,?_,?_⟩
  · simpa only [hlog,WeightedColumns.canonical] using hb
  · intro Z hZ
    have hp1 : G1.probability=gibbsWeight G1.eigenval := rfl
    rw [hp1]
    simpa only [R.firstFlow_dual_raw] using hh1 Z hZ
  · intro Z hZ
    have hp2 : G2.probability=gibbsWeight G2.eigenval := rfl
    rw [hp2]
    simpa only [R.secondFlow_dual_raw] using hh2 Z hZ
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
open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.Regularization
open scoped BigOperators ComplexConjugate
open QuantumTrace Annihilation


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.Regularization.minimum_spectral_pairing_balance := @_root_.OAI.EntropyPhotonNumber.Regularization.minimum_spectral_pairing_balance
