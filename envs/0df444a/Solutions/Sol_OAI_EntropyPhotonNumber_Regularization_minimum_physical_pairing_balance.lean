-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.Regularization.minimum_physical_pairing_balance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:11:54.31192+00:00
-- url     : https://prove2.me/submissions/8af6f45a-e96e-4c1c-87cd-243d698a7073

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/PhysicalMinimum.lean:L648-L704
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.Regularization.minimum_physical_pairing_balance. The node keeps its source
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
import Theorems.Thm_OAI_BKM_vector_id_inner
import Theorems.Thm_OAI_BeamLadder_radial_covariance
import Theorems.Thm_OAI_EntropyPhotonNumber_GibbsData_exact_logarithmic_identity
import Theorems.Thm_OAI_EntropyPhotonNumber_exists_faithful_eigenbasis_of_thermal_le
import Theorems.Thm_OAI_EntropyPhotonNumber_logarithmic_slice_representation
import Theorems.Thm_OAI_EntropyPhotonNumber_minimum_all_blocks_hessian_data
import Theorems.Thm_OAI_QuantumTrace_positive_eq_of_quadratic
import Theorems.Thm_OAI_TensorLp_liftLeft_positive
import Theorems.Thm_OAI_WeightedGenerator_pairing_hasSum

-- ---- from OAI.Analysis.QuantumTrace.Basic ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open Filter

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open Filter ContinuousLinearMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End Submodule
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End
open scoped ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section

open Filter Topology
open scoped Classical
variable {ι : Type*}
end

section
open Filter Topology
open scoped Classical
variable {ι : Type*}

end

section
open Filter Topology
variable {ι : Type*}

theorem inversePower_mul (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p q : ℕ) :
    inversePower s hs p * inversePower s hs q = inversePower s hs (p+q) := by
  ext x i
  simp only [mul_apply_eq_comp, inversePower_apply, pow_add, mul_inv,
    Complex.ofReal_mul, mul_assoc]

end

section
open ContinuousLinearMap Module.End Submodule
universe v
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open Filter Topology
variable {ι : Type*}

end

section
open Filter Topology

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*}

end

section
variable {ι J : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end

open scoped BigOperators ComplexConjugate
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end QuantumTrace

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace QuantumTrace
variable {ι J : Type*}

end QuantumTrace

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Gibbs ----
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace TraceEnsemble

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber

end EntropyPhotonNumber

namespace WeightedShift
open scoped BigOperators ComplexConjugate
variable {I K : Type*} [DecidableEq K]

end WeightedShift

namespace EntropyPhotonNumber
open QuantumTrace WeightedShift Annihilation
variable {n : ℕ}

end EntropyPhotonNumber

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped ComplexConjugate
variable {n : ℕ}

theorem inner_inverse_pair (a b : ℕ) (x y : Fock n) :
    inner ℂ (inverseWeight a x) (inverseWeight b y)=inner ℂ x (inverseWeight (a+b) y) := by
  rw [inverseWeight_add, ContinuousLinearMap.comp_apply]
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (inverseWeight_selfAdjoint a) x (inverseWeight b y)

theorem gain_trace (j : Fin n) (u : Bool) (x : Fock n) :
    inner ℂ (gain j u x) (inverseWeight 4 (gain j u x))=
      (‖unweightedGain j u (inverseWeight 2 x)‖^2:ℝ) := by
  have he : inverseWeight 2 (gain j u x)=unweightedGain j u (inverseWeight 2 x) :=
    congrArg (fun T : Fock n →L[ℂ] Fock n => T x) (gain_factor j u)
  rw [← inner_inverse_pair 2 2, he]
  rw [inner_self_eq_norm_sq_to_K]
  exact (map_pow Complex.ofRealHom _ 2).symm

theorem mode_trace_left (j : Fin n) (u : Bool) (x : Fock n) :
    inner ℂ (inverseWeight 1 x) (inverseWeight 4 (modeBound j u x))=
      (‖unweightedGain j u (inverseWeight 2 x)‖^2:ℝ) := by
  calc
    _ = inner ℂ (inverseWeight 3 x) (inverseWeight 2 (modeBound j u x)) := by
      rw [inner_inverse_pair, inner_inverse_pair]
    _ = _ := mode_quadratic j u x

theorem mode_trace_right (j : Fin n) (u : Bool) (x : Fock n) :
    inner ℂ (modeBound j u x) (inverseWeight 4 (inverseWeight 1 x))=
      (‖unweightedGain j u (inverseWeight 2 x)‖^2:ℝ) := by
  have hh := congrArg (starRingEnd ℂ) (mode_trace_left j u x)
  calc
    _ = inner ℂ (inverseWeight 4 (modeBound j u x)) (inverseWeight 1 x) :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (inverseWeight_selfAdjoint 4) (modeBound j u x) (inverseWeight 1 x)).symm
    _ = _ := by simpa only [inner_conj_symm, Complex.conj_ofReal] using hh
end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

theorem pairing_inverse_zero (r : ℝ) (x : I → Fock n) : pairing r x (inverseWeight 4)=0 := by
  unfold pairing CrossEnsemble.pairing
  simp only [gain_trace, mode_trace_left, mode_trace_right]
  apply Finset.sum_eq_zero
  intro j _hj
  ring

end WeightedGenerator

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation
variable {n : ℕ} {J : Type*}

end EntropyPhotonNumber

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
variable {n : ℕ} {I J K : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber
open Annihilation CrossEnsemble
variable {n : ℕ} {J : Type*}

end EntropyPhotonNumber

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation

variable {n : ℕ} {k : ℝ} {ρ : State n}

namespace GibbsData
variable (G : GibbsData n k ρ)

end GibbsData
end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)

end GibbsData
end EntropyPhotonNumber

end

end OAI

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

theorem inverse_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) :
    inverse ∘L (beamUnitary (n:=n) η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L inverse :=
  radial_covariance η hη (fun t => t⁻¹) 1 (by norm_num) inverse_bound

theorem covariance_inverse_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x : JointFock n) :
    inverse (beamUnitary η hη x)=beamUnitary η hη (inverse x) :=
  congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (inverse_covariance η hη)

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

-- ---- from OAI.InformationTheory.PhotonNumber.BeamForms ----
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

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end CrossEnsemble

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

theorem tensorRatioCLM_norm (z : JointFock n) : ‖tensorRatioCLM z‖≤‖z‖ := by
  have hb : ‖tensorRatioCLM z‖ ≤ 1*‖z‖ := WeightedShift.pull_bound id Function.injective_id
    (fun ke : NumberIndex n × NumberIndex n => ((tensorRatio ke)^2:ℂ))
    1 (by norm_num) (fun ke => by simpa only [Complex.real_smul,mul_one,Complex.ofReal_pow] using ratioSquare_norm (tensorRatio_mem ke)) z
  simpa only [one_mul] using hb

theorem retainedRatioCLM_norm (z : JointFock n) : ‖retainedRatioCLM z‖≤‖z‖ := by
  have hb : ‖retainedRatioCLM z‖ ≤ 1*‖z‖ := WeightedShift.pull_bound id Function.injective_id
    (fun ke : NumberIndex n × NumberIndex n => ((retainedRatio ke)^2:ℂ))
    1 (by norm_num) (fun ke => by simpa only [Complex.real_smul,mul_one,Complex.ofReal_pow] using ratioSquare_norm (retainedRatio_mem ke)) z
  simpa only [one_mul] using hb

theorem weightedColumn_norm (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : Fock n) :
    ‖weightedColumn η hη y‖≤‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y)
  intro x
  rw [weightedColumn_apply]
  calc
    _ ≤ ‖beamUnitary η hη (tensorRatioCLM (tensor x y))‖ := retainedRatioCLM_norm _
    _ = ‖tensorRatioCLM (tensor x y)‖ := (beamUnitary η hη).norm_map _
    _ ≤ ‖tensor x y‖ := tensorRatioCLM_norm _
    _ = ‖y‖*‖x‖ := by rw [tensor_norm,mul_comm]

theorem weightedColumn_summable {I : Type*} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : I → Fock n) (hy : Summable (fun i => ‖y i‖^2)) :
    Summable (fun i => ‖weightedColumn η hη (y i)‖^2) :=
  hy.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i =>
    pow_le_pow_left₀ (norm_nonneg _) (weightedColumn_norm η hη (y i)) 2)

theorem tensorRatio_inverse (x y : Fock n) :
    inverse (inverse (tensorRatioCLM (tensor x y)))=tensor (inverseWeight 2 x) (inverseWeight 2 y) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  have hw : (W (k,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (k,e)] : W (k,e)≠0)
  have hk : (numberWeight k:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le k] : numberWeight k≠0)
  have he : (numberWeight e:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le e] : numberWeight e≠0)
  simp only [inverse_apply,tensorRatioCLM,WeightedShift.pullCLM_apply,tensorRatio,
    id_eq,tensor_apply,inverseWeight_apply,Complex.ofReal_div,Complex.ofReal_mul]
  field_simp

theorem retainedRatio_inverse (z : JointFock n) :
    liftLeft (inverseWeight 2) (retainedRatioCLM z)=inverse (inverse z) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  have hw : (W (k,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (k,e)] : W (k,e)≠0)
  have hk : (numberWeight k:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le k] : numberWeight k≠0)
  simp only [liftLeft_apply,inverseWeight_apply,slice_apply,retainedRatioCLM,
    WeightedShift.pullCLM_apply,retainedRatio,id_eq,inverse_apply,Complex.ofReal_div]
  field_simp

theorem weightedColumn_inverse (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x y : Fock n) :
    liftLeft (inverseWeight 2) (weightedColumn η hη y x)=
      beamUnitary η hη (tensor (inverseWeight 2 x) (inverseWeight 2 y)) := by
  rw [weightedColumn_apply]
  rw [retainedRatio_inverse,covariance_inverse_apply,covariance_inverse_apply,tensorRatio_inverse]

end BeamLadder

namespace EnsemblePullback

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I : Type*}

theorem compression_norm (V : E →L[ℂ] F) (Z : F →L[ℂ] F) :
    ‖compression V Z‖ ≤ ‖Z‖*‖V‖^2 := by
  calc
    _ ≤ ‖V.adjoint‖*‖Z ∘L V‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖V.adjoint‖*(‖Z‖*‖V‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

theorem summable_compression {V : I → E →L[ℂ] F} (hV : Summable (fun i => ‖V i‖^2))
    (Z : F →L[ℂ] F) : Summable (fun i => compression (V i) Z) := by
  apply Summable.of_norm_bounded (hV.mul_left ‖Z‖)
  exact fun i => compression_norm _ _

theorem compression_entry (V : E →L[ℂ] F) (Z : F →L[ℂ] F) (x y : E) :
    inner ℂ x (compression V Z y) = inner ℂ (V x) (Z (V y)) := by
  exact ContinuousLinearMap.adjoint_inner_right V x (Z (V y))

theorem hasSum_entry {V : I → E →L[ℂ] F} (hV : Summable (fun i => ‖V i‖^2))
    (Z : F →L[ℂ] F) (x y : E) :
    HasSum (fun i => inner ℂ (V i x) (Z (V i y))) (inner ℂ x (pullback V Z y)) := by
  convert! (((summable_compression hV Z).hasSum).mapL
    (ContinuousLinearMap.apply ℂ E y)).mapL (innerSL ℂ x) using 1
  ext i
  exact (compression_entry _ _ _ _).symm

theorem compression_positive (V : E →L[ℂ] F) {Z : F →L[ℂ] F} (hZ : Z.IsPositive) :
    (compression V Z).IsPositive := hZ.adjoint_conj V

theorem pullback_positive (V : I → E →L[ℂ] F) {Z : F →L[ℂ] F} (hZ : Z.IsPositive) :
    (pullback V Z).IsPositive := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
  apply tsum_nonneg
  exact fun i => (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (compression_positive _ hZ)

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I J : Type*}

end EnsemblePullback

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace CrossEnsemble
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {I : Type*}
end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I : Type*}

end BeamLadder

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I K : Type*}

end WeightedGenerator

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

theorem weightedColumnRight_norm (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : Fock n) :
    ‖weightedColumnRight η hη y‖≤‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y)
  intro x
  rw [weightedColumnRight_apply]
  calc
    _ ≤ ‖beamUnitary η hη (tensorRatioCLM (tensor y x))‖ := retainedRatioCLM_norm _
    _ = ‖tensorRatioCLM (tensor y x)‖ := (beamUnitary η hη).norm_map _
    _ ≤ ‖tensor y x‖ := tensorRatioCLM_norm _
    _ = ‖y‖*‖x‖ := tensor_norm y x

theorem weightedColumnRight_summable (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : J → Fock n) (hy : Summable (fun i => ‖y i‖^2)) :
    Summable (fun i => ‖weightedColumnRight η hη (y i)‖^2) :=
  hy.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i =>
    pow_le_pow_left₀ (norm_nonneg _) (weightedColumnRight_norm η hη (y i)) 2)

theorem weightedColumnRight_inverse (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x y : Fock n) :
    liftLeft (inverseWeight 2) (weightedColumnRight η hη y x)=
      beamUnitary η hη (tensor (inverseWeight 2 y) (inverseWeight 2 x)) := by
  rw [weightedColumnRight_apply,retainedRatio_inverse,covariance_inverse_apply,
    covariance_inverse_apply,tensorRatio_inverse]

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I : Type*}

end CrossEnsemble

end

end OAI

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

theorem mixture_replacement_le {n : ℕ} (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1) (ρ τ : State n) :
    (κ : ℂ) • τ.op ≤ (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ ρ τ).op := by
  have hp := ρ.positive.smul_of_nonneg (c := ((1-κ : ℝ) : ℂ))
    (by exact_mod_cast sub_nonneg.mpr hκ.2)
  have he : 1-(1-κ) = κ := by ring
  simpa only [mixture, he, add_sub_cancel_right] using
    le_add_of_nonneg_left ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp)

end

open QuantumTrace Annihilation
variable {n : ℕ}

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

theorem dual_id (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2)) :
    dual V hV (ContinuousLinearMap.id ℂ H)=ContinuousLinearMap.id ℂ E := by
  have he : acted V hV (ContinuousLinearMap.id ℂ H)=analysis V hV := by
    ext x i
    rfl
  rw [dual, he]
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
  intro x
  have hh : ‖analysis V hV x‖^2=‖x‖^2 := (wave_square V (fun y => (hV y).summable) x).trans (hV x).tsum_eq
  nlinarith [norm_nonneg (analysis V hV x), norm_nonneg x]
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

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace TensorLp

end

open QuantumTrace

theorem energyInverse_mul_three {n : ℕ} (x : Fock n) :
    energyInverse n (inversePower rootNumberWeight rootNumberWeight_one_le 3 x) =
      inversePower rootNumberWeight rootNumberWeight_one_le 4 x := by
  exact congrArg (fun T : Fock n →L[ℂ] Fock n => T x)
    (inversePower_mul rootNumberWeight rootNumberWeight_one_le 1 3)

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

-- ---- from OAI.InformationTheory.PhotonNumber.Contraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

namespace EnsembleL2

section
open scoped BigOperators ComplexConjugate
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end

open scoped BigOperators
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace EnsembleL2
open scoped ComplexConjugate
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace BKM
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace TensorLp
open KrausBounded
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate

end EntropyPhotonNumber

namespace EnsembleL2
open scoped ComplexConjugate
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate
variable {n : ℕ}

end EntropyPhotonNumber

namespace EnsembleL2
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace EntropyPhotonNumber
open ThermalSpectral ThermalSpectral.Space
variable {n : ℕ}

end EntropyPhotonNumber

namespace BKM

section
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem entry_sub (b : HilbertBasis J ℂ E) (Z T : E →L[ℂ] E) (i j : J) :
    entry b (Z-T) i j=entry b Z i j-entry b T i j := by simp [entry]
theorem entry_id [DecidableEq J] (b : HilbertBasis J ℂ E) (i j : J) :
    entry b (ContinuousLinearMap.id ℂ E) i j = if i=j then 1 else 0 := by
  exact orthonormal_iff_ite.mp b.orthonormal i j

theorem mean_id (b : HilbertBasis J ℂ E) (p : J → ℝ) (hs : HasSum p 1) :
    mean b p (ContinuousLinearMap.id ℂ E)=1 := by
  classical
  simp only [mean, entry_id, ite_true, mul_one]
  exact (hs.mapL Complex.ofRealCLM).tsum_eq

end

section
open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem mean_neg (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) :
    mean b p (-Z) = -mean b p Z := by
  simpa only [neg_one_smul, neg_one_mul] using mean_smul b p (-1) Z

theorem mean_sub (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    (Z T : E →L[ℂ] E) : mean b p (Z-T)=mean b p Z-mean b p T := by
  rw [sub_eq_add_neg, mean_add b p hp hs, mean_neg, sub_eq_add_neg]

theorem mean_center (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : HasSum p 1)
    (Z : E →L[ℂ] E) : mean b p (center b p Z)=0 := by
  rw [center, mean_sub b p hp hs.summable, mean_smul, mean_id b p hs, mul_one, sub_self]

end

open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem mean_rankOne [DecidableEq J] (b : HilbertBasis J ℂ E) (p : J → ℝ) (i j : J) :
    mean b p (InnerProductSpace.rankOne ℂ (b i) (b j))=if i=j then (p i:ℂ) else 0 := by
  classical
  rw [mean, tsum_eq_single i]
  · simp only [entry, InnerProductSpace.rankOne_apply, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal, ite_true, mul_one]
    split_ifs <;> simp_all
  · intro k hk
    simp only [entry, InnerProductSpace.rankOne_apply, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal, ite_eq_right hk, mul_zero]

end BKM

namespace CenteredTests
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem generator_eq_center (b : HilbertBasis J ℂ E) (p : J → ℝ) (ij : J × J) :
    generator b p ij=BKM.center b p (InnerProductSpace.rankOne ℂ (b ij.1) (b ij.2)) := by
  classical
  rw [BKM.center, BKM.mean_rankOne]
  rfl

theorem mean_eq_zero (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : HasSum p 1)
    {Z : E →L[ℂ] E} (hZ : Z ∈ operatorSpace b p) : BKM.mean b p Z=0 := by
  obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hZ
  have hc : (c.sum fun ij a => a • generator b p ij)=
      BKM.centerLM b p hp hs.summable (c.sum fun ij a => a • InnerProductSpace.rankOne ℂ (b ij.1) (b ij.2)) := by
    simp only [Finsupp.sum, map_sum, map_smul, BKM.centerLM_apply, ← generator_eq_center]
  rw [hc, BKM.centerLM_apply]
  exact BKM.mean_center b p hp hs _

end CenteredTests

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace EntropyPhotonNumber
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space
variable {n : ℕ}

end EntropyPhotonNumber

namespace BKM
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace EntropyPhotonNumber
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space ThermalMetric
variable {n : ℕ}

end EntropyPhotonNumber

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

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

 theorem KrausFlow.dual_add (F : KrausFlow n) (Z T : Fock n →L[ℂ] Fock n) :
    F.dual (Z+T)=F.dual Z+F.dual T := KrausBounded.dual_add F.V F.norm Z T
 theorem KrausFlow.dual_smul (F : KrausFlow n) (c : ℂ) (Z : Fock n →L[ℂ] Fock n) :
    F.dual (c • Z)=c • F.dual Z := KrausBounded.dual_smul F.V F.norm c Z
 theorem KrausFlow.dual_sub (F : KrausFlow n) (Z T : Fock n →L[ℂ] Fock n) :
    F.dual (Z-T)=F.dual Z-F.dual T := by
  have hneg (operator : Fock n →L[ℂ] Fock n) : (-1:ℂ) • operator = -operator := by
    apply ContinuousLinearMap.ext
    intro vector
    simp only [smul_apply, neg_apply, neg_one_smul]
  rw [sub_eq_add_neg, ← hneg T, F.dual_add, F.dual_smul, hneg, ← sub_eq_add_neg]
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

theorem vector_sub (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (Z T : E →L[ℂ] E) : vector b p hp hs (Z-T)=vector b p hp hs Z-vector b p hp hs T := by
  apply lp.ext
  ext ij
  simp [entry_sub, mul_sub]

theorem vector_smul (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (c : ℂ) (Z : E →L[ℂ] E) : vector b p hp hs (c • Z)=c • vector b p hp hs Z := by
  apply lp.ext
  ext ij
  simp [entry_smul, mul_left_comm]

theorem vector_norm (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (Z : E →L[ℂ] E) : ‖vector b p hp hs Z‖^2=quadratic b p Z := by
  have hh := lp.hasSum_norm (p := (2:ENNReal)) (by norm_num) (vector b p hp hs Z)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, vector_apply, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (logMean_pos (hp _) (hp _)).le] at hh
  exact hh.tsum_eq.symm
theorem vector_id_norm (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : HasSum p 1) :
    ‖vector b p hp hs.summable (ContinuousLinearMap.id ℂ E)‖^2=1 := by
  have hh := vector_id_inner b p hp hs.summable (ContinuousLinearMap.id ℂ E)
  rw [mean_id b p hs, inner_self_eq_norm_sq_to_K] at hh
  have hh' := congrArg Complex.re hh
  change ((‖vector b p hp hs.summable (ContinuousLinearMap.id ℂ E)‖ : ℂ)^2).re=1 at hh'
  rw [← Complex.ofReal_pow, Complex.ofReal_re] at hh'
  exact hh'
theorem quadratic_center (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : HasSum p 1)
    (Z : E →L[ℂ] E) : quadratic b p (center b p Z)=variance b p Z := by
  rw [← vector_norm b p hp hs.summable, center, vector_sub, vector_smul, norm_sub_sq (𝕜 := ℂ)]
  have hi : inner ℂ (vector b p hp hs.summable Z) (vector b p hp hs.summable (ContinuousLinearMap.id ℂ E))=
      conj (mean b p Z) := by
    rw [← inner_conj_symm, vector_id_inner]
  rw [vector_norm, inner_smul_right, hi, norm_smul, mul_pow, vector_id_norm b p hp hs, mul_one]
  simp only [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  change quadratic b p Z-2*Complex.normSq (mean b p Z)+Complex.normSq (mean b p Z)=variance b p Z
  unfold variance
  ring

end

open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem center_id (b : HilbertBasis J ℂ E) (p : J → ℝ) (hs : HasSum p 1) :
    center b p (ContinuousLinearMap.id ℂ E)=0 := by simp [center, mean_id b p hs]

theorem center_sub_scalar (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : HasSum p 1)
    (Z : E →L[ℂ] E) (c : ℂ) :
    center b p (Z-c • ContinuousLinearMap.id ℂ E)=center b p Z := by
  change centerLM b p hp hs.summable (Z-c • ContinuousLinearMap.id ℂ E)=_
  simp only [map_sub, map_smul, centerLM_apply, center_id b p hs, smul_zero, sub_zero]

variable [CompleteSpace E]

theorem variance_sub_scalar (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : HasSum p 1)
    (Z : E →L[ℂ] E) (c : ℂ) :
    variance b p (Z-c • ContinuousLinearMap.id ℂ E)=variance b p Z := by
  rw [← quadratic_center b p hp hs, center_sub_scalar b p (fun j => (hp j).le) hs,
    quadratic_center b p hp hs]
end BKM

namespace CenteredTests
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem exists_block [DecidableEq J] (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    {Z : E →L[ℂ] E} (hZ : Z ∈ operatorSpace b p) :
    ∃ (s : Finset J) (M : Matrix s s ℂ),
      Z=BKM.center b p (FiniteBlock.block (BKM.reindexBasis b (Equiv.sumCompl (· ∈ s))) M) := by
  classical
  obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hZ
  let s := c.support.biUnion (fun ij => {ij.1,ij.2})
  have hsub : c.support ⊆ s ×ˢ s := by
    intro ij hij
    simp only [Finset.mem_product]
    constructor
    · exact Finset.mem_biUnion.mpr ⟨ij,hij,by simp⟩
    · exact Finset.mem_biUnion.mpr ⟨ij,hij,by simp⟩
  refine ⟨s, (fun i j => c (i.val,j.val)), ?_⟩
  have hc : (c.sum fun ij a => a • generator b p ij)=
      BKM.centerLM b p hp hs (c.sum fun ij a => a • InnerProductSpace.rankOne ℂ (b ij.1) (b ij.2)) := by
    simp only [Finsupp.sum, map_sum, map_smul, BKM.centerLM_apply, ← generator_eq_center]
  rw [hc, BKM.centerLM_apply]
  congr 1
  rw [c.sum_of_support_subset hsub _ (by intro ij; simp)]
  simp only [FiniteBlock.block, BKM.reindexBasis_apply, Equiv.sumCompl_apply_inl]
  rw [Finset.sum_product]
  simp only [← Finset.sum_coe_sort s]
end CenteredTests

namespace EntropyPhotonNumber

section
open QuantumTrace DiagonalForms.System
variable {n : ℕ} {I J : Type*} [DecidableEq J]

theorem KrausFlow.dual_id (F : KrausFlow n) :
    F.dual (ContinuousLinearMap.id ℂ (Fock n))=ContinuousLinearMap.id ℂ (Fock n) :=
  KrausBounded.dual_id F.V F.norm

theorem blocks_to_centered_hessian
    (F : KrausFlow n) (b : HilbertBasis I ℂ (Fock n)) (p : I → ℝ)
    (hp : ∀ i, 0 < p i) (hs : HasSum p 1)
    (d : HilbertBasis J ℂ (Fock n)) (q : J → ℝ) (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (a κ : ℝ)
    (hh : ∀ (s : Finset J) (M : Matrix s s ℂ),
      (1-κ)^2*BKM.variance b p (F.dual (FiniteBlock.block (BKM.reindexBasis d (Equiv.sumCompl (· ∈ s))) M)) ≤
        a*BKM.variance d q (FiniteBlock.block (BKM.reindexBasis d (Equiv.sumCompl (· ∈ s))) M))
    (Z : Fock n →L[ℂ] Fock n) (hZ : Z ∈ CenteredTests.operatorSpace d q) :
    (1-κ)^2*BKM.quadratic b p (BKM.center b p (F.dual Z)) ≤ a*BKM.quadratic d q Z := by
  rw [BKM.quadratic_center b p hp hs]
  have hz : BKM.variance d q Z=BKM.quadratic d q Z := by
    rw [BKM.variance, CenteredTests.mean_eq_zero d q (fun j => (hq j).le) ht hZ]
    simp
  rw [← hz]
  obtain ⟨s,M,rfl⟩ := CenteredTests.exists_block d q (fun j => (hq j).le) ht.summable hZ
  simp only [BKM.center, F.dual_sub, F.dual_smul, F.dual_id,
    BKM.variance_sub_scalar b p hp hs, BKM.variance_sub_scalar d q hq ht]
  exact hh s M
end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J : Type*} [DecidableEq J]
theorem minimum_centered_hessian_data
    (F : KrausFlow n) (τ : State n) {r : ℝ} (hr : 0 < r) (hτ : τ = thermalState n r hr)
    (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1) (hκ0 : 0 < κ)
    (c a β ζ : ℝ) (hc : 0 < c) (ha : 0 < a) (hβ : 0 ≤ β) (hζ : 0 < ζ)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (d : HilbertBasis J ℂ (Fock n)) (q : J → ℝ)
    (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-a*entropy ρ+
        β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-a*entropy σ+
        β*energy σ+ζ*numberMoment 4 σ) :
    ∃ G : GibbsData n (ζ/a) ρ,
      (∀ x, ENNReal.ofReal (inner ℂ x (G.B x)).re =
        ENNReal.ofReal (c*(1-κ)/a)*
          sliceMoment d (fun j => ENNReal.ofReal (-Real.log (q j))) F.V (energyInverse n x)+
        ENNReal.ofReal (β/a)*numberVectorMoment (energyInverse n x)) ∧
      ∀ (Z : Fock n →L[ℂ] Fock n),
      Z ∈ CenteredTests.operatorSpace d q →
      (1-κ)^2*BKM.quadratic G.basis (gibbsWeight G.eigenval)
        (BKM.center G.basis (gibbsWeight G.eigenval) (F.dual Z)) ≤
      (a/c)*BKM.quadratic d q Z := by
  obtain ⟨G,hform,hG⟩ := minimum_all_blocks_hessian_data F τ hr hτ κ hκ hκ0 c a β ζ hc ha hβ hζ ρ hmρ
    d q hq ht he0 hmin
  let _ := G.nonempty
  refine ⟨G, hform, ?_⟩
  exact blocks_to_centered_hessian F G.basis (gibbsWeight G.eigenval)
    (gibbsWeight_pos G.eigenval G.heat) (gibbsWeight_hasSum G.eigenval G.heat) d q hq ht (a/c) κ hG
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

theorem positive_quadratic_slices {Z : H A →L[ℂ] H A} (hZ : Z.IsPositive)
    (x : H (A × B)) :
    ENNReal.ofReal (inner ℂ x (liftLeft Z x)).re=
      ∑' b, ENNReal.ofReal (inner ℂ (slice x b) (Z (slice x b))).re := by
  have hs : HasSum (fun b => (inner ℂ (slice x b) (Z (slice x b))).re)
      (inner ℂ x (liftLeft Z x)).re := by
    simpa only [Complex.reCLM_apply,slice_liftLeft] using
      (hasSum_slice_inner x (liftLeft Z x)).mapL Complex.reCLM
  have hn (b : B) : 0 ≤ (inner ℂ (slice x b) (Z (slice x b))).re :=
    hZ.re_inner_nonneg_right (slice x b)
  rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hn hs.summable]
end TensorLp

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {J : Type*}

theorem weightedConditional_form (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : J → Fock n) (hy : Summable (fun j => ‖y j‖^2))
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (Q : Fock n → ℝ≥0∞)
    (hQ : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=Q (inverseWeight 2 x))
    (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (weightedConditional η hη y B x)).re=
      ∑' j, ∑' e, Q (slice (beamUnitary η hη
        (tensor (inverseWeight 2 x) (inverseWeight 2 (y j)))) e) := by
  have hp := liftLeft_positive (B:=NumberIndex n) hB
  have hs : HasSum (fun j => (inner ℂ (weightedColumn η hη (y j) x)
      (liftLeft B (weightedColumn η hη (y j) x))).re)
      (inner ℂ x (weightedConditional η hη y B x)).re := by
    exact (EnsemblePullback.hasSum_entry (weightedColumn_summable η hη y hy)
      (liftLeft B) x x).mapL Complex.reCLM
  have hn (j : J) : 0 ≤ (inner ℂ (weightedColumn η hη (y j) x)
      (liftLeft B (weightedColumn η hη (y j) x))).re :=
    hp.re_inner_nonneg_right (weightedColumn η hη (y j) x)
  rw [← hs.tsum_eq,ENNReal.ofReal_tsum_of_nonneg hn hs.summable]
  apply tsum_congr
  intro j
  rw [positive_quadratic_slices hB]
  apply tsum_congr
  intro e
  rw [hQ]
  congr 1
  rw [← slice_liftLeft,weightedColumn_inverse]
theorem weightedConditionalRight_form (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : J → Fock n) (hy : Summable (fun j => ‖y j‖^2))
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (Q : Fock n → ℝ≥0∞)
    (hQ : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=Q (inverseWeight 2 x))
    (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (weightedConditionalRight η hη y B x)).re=
      ∑' j, ∑' e, Q (slice (beamUnitary η hη
        (tensor (inverseWeight 2 (y j)) (inverseWeight 2 x))) e) := by
  have hp := liftLeft_positive (B:=NumberIndex n) hB
  have hs : HasSum (fun j => (inner ℂ (weightedColumnRight η hη (y j) x)
      (liftLeft B (weightedColumnRight η hη (y j) x))).re)
      (inner ℂ x (weightedConditionalRight η hη y B x)).re := by
    exact (EnsemblePullback.hasSum_entry (weightedColumnRight_summable η hη y hy)
      (liftLeft B) x x).mapL Complex.reCLM
  have hn (j : J) : 0 ≤ (inner ℂ (weightedColumnRight η hη (y j) x)
      (liftLeft B (weightedColumnRight η hη (y j) x))).re :=
    hp.re_inner_nonneg_right (weightedColumnRight η hη (y j) x)
  rw [← hs.tsum_eq,ENNReal.ofReal_tsum_of_nonneg hn hs.summable]
  apply tsum_congr
  intro j
  rw [positive_quadratic_slices hB]
  apply tsum_congr
  intro e
  rw [hQ]
  congr 1
  rw [← slice_liftLeft,weightedColumnRight_inverse]
end BeamLadder

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ}
theorem weightedConditional_root_form (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (σ : State n) (hm : FiniteMoment 4 σ)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (Q : Fock n → ℝ≥0∞)
    (hQ : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=Q (inverseWeight 2 x))
    (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (weightedConditional η hη (weightedRoot 2 σ hm) B x)).re=
      ∑' eb, Q (firstKraus η hη σ eb (inverseWeight 2 x)) := by
  rw [weightedConditional_form η hη _ (weightedRoot_summable 2 σ hm) B hB Q hQ]
  simp only [inverse_weightedRoot,firstKraus_apply,ENNReal.tsum_prod']
  exact ENNReal.tsum_comm

theorem weightedConditionalRight_root_form (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (σ : State n) (hm : FiniteMoment 4 σ)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (Q : Fock n → ℝ≥0∞)
    (hQ : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=Q (inverseWeight 2 x))
    (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (weightedConditionalRight η hη (weightedRoot 2 σ hm) B x)).re=
      ∑' eb, Q (secondKraus η hη σ eb (inverseWeight 2 x)) := by
  rw [weightedConditionalRight_form η hη _ (weightedRoot_summable 2 σ hm) B hB Q hQ]
  simp only [inverse_weightedRoot,secondKraus_apply,ENNReal.tsum_prod']
  exact ENNReal.tsum_comm

namespace GibbsData
variable {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end GibbsData

namespace WeightedColumns

end WeightedColumns

theorem weightedConditional_positive (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    {J : Type*} (y : J → Fock n) {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) :
    (weightedConditional η hη y B).IsPositive :=
  EnsemblePullback.pullback_positive _ (liftLeft_positive hB)

theorem weightedConditionalRight_positive (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    {J : Type*} (y : J → Fock n) {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) :
    (weightedConditionalRight η hη y B).IsPositive :=
  EnsemblePullback.pullback_positive _ (liftLeft_positive hB)

theorem weightedConditional_twopass_form (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τD : State n) (hσ : FiniteMoment 4 σ) (hD : FiniteMoment 4 τD)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (Q : Fock n → ℝ≥0∞)
    (hQ : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=Q (inverseWeight 2 x))
    (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (weightedConditional η hη (weightedRoot 2 σ hσ)
        (weightedConditional θ hθ (weightedRoot 2 τD hD) B) x)).re=
      ∑' ij, Q (composeKraus (firstKraus θ hθ τD) (firstKraus η hη σ) ij (inverseWeight 2 x)) := by
  rw [weightedConditional_root_form η hη σ hσ _
    (weightedConditional_positive θ hθ _ hB)
    (fun z => ∑' e, Q (firstKraus θ hθ τD e z))
    (weightedConditional_root_form θ hθ τD hD B hB Q hQ)]
  simp only [composeKraus,ContinuousLinearMap.comp_apply]
  rw [ENNReal.tsum_prod' (f := fun ij :
    (NumberIndex n × NumberIndex n) × (NumberIndex n × NumberIndex n) =>
      Q (firstKraus θ hθ τD ij.1 (firstKraus η hη σ ij.2 (inverseWeight 2 x))))]
  exact ENNReal.tsum_comm

theorem weightedConditionalRight_twopass_form (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τD : State n) (hσ : FiniteMoment 4 σ) (hD : FiniteMoment 4 τD)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (Q : Fock n → ℝ≥0∞)
    (hQ : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=Q (inverseWeight 2 x))
    (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (weightedConditionalRight η hη (weightedRoot 2 σ hσ)
        (weightedConditional θ hθ (weightedRoot 2 τD hD) B) x)).re=
      ∑' ij, Q (composeKraus (firstKraus θ hθ τD) (secondKraus η hη σ) ij (inverseWeight 2 x)) := by
  rw [weightedConditionalRight_root_form η hη σ hσ _
    (weightedConditional_positive θ hθ _ hB)
    (fun z => ∑' e, Q (firstKraus θ hθ τD e z))
    (weightedConditional_root_form θ hθ τD hD B hB Q hQ)]
  simp only [composeKraus,ContinuousLinearMap.comp_apply]
  rw [ENNReal.tsum_prod' (f := fun ij :
    (NumberIndex n × NumberIndex n) × (NumberIndex n × NumberIndex n) =>
      Q (firstKraus θ hθ τD ij.1 (secondKraus η hη σ ij.2 (inverseWeight 2 x))))]
  exact ENNReal.tsum_comm

theorem spectral_physical_twopass_identification {J : Type*}
    (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τD : State n) (hσ : FiniteMoment 4 σ) (hD : FiniteMoment 4 τD)
    (b : HilbertBasis J ℂ (Fock n)) (w : J → ℝ≥0∞)
    (B C : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (hC : C.IsPositive)
    (hBe : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=basisMoment b w (inverseWeight 2 x))
    (hCe : ∀ x, ENNReal.ofReal (inner ℂ x (C x)).re=
      sliceMoment b w (composeKraus (firstKraus θ hθ τD) (firstKraus η hη σ))
        (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) :
    C=weightedConditional η hη (weightedRoot 2 σ hσ)
      (weightedConditional θ hθ (weightedRoot 2 τD hD) B) := by
  have hp := weightedConditional_positive η hη (weightedRoot 2 σ hσ)
    (weightedConditional_positive θ hθ (weightedRoot 2 τD hD) hB)
  apply positive_eq_of_quadratic hC hp
  intro x
  apply (ENNReal.ofReal_eq_ofReal_iff (hC.re_inner_nonneg_right x) (hp.re_inner_nonneg_right x)).mp
  change ENNReal.ofReal (inner ℂ x (C x)).re =
    ENNReal.ofReal (inner ℂ x (weightedConditional η hη (weightedRoot 2 σ hσ)
      (weightedConditional θ hθ (weightedRoot 2 τD hD) B) x)).re
  rw [hCe,inversePower_root_four,weightedConditional_twopass_form η θ hη hθ σ τD hσ hD B hB
    (basisMoment b w) hBe]
  rfl

theorem spectral_physical_right_twopass_identification {J : Type*}
    (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τD : State n) (hσ : FiniteMoment 4 σ) (hD : FiniteMoment 4 τD)
    (b : HilbertBasis J ℂ (Fock n)) (w : J → ℝ≥0∞)
    (B C : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (hC : C.IsPositive)
    (hBe : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=basisMoment b w (inverseWeight 2 x))
    (hCe : ∀ x, ENNReal.ofReal (inner ℂ x (C x)).re=
      sliceMoment b w (composeKraus (firstKraus θ hθ τD) (secondKraus η hη σ))
        (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) :
    C=weightedConditionalRight η hη (weightedRoot 2 σ hσ)
      (weightedConditional θ hθ (weightedRoot 2 τD hD) B) := by
  have hp := weightedConditionalRight_positive η hη (weightedRoot 2 σ hσ)
    (weightedConditional_positive θ hθ (weightedRoot 2 τD hD) hB)
  apply positive_eq_of_quadratic hC hp
  intro x
  apply (ENNReal.ofReal_eq_ofReal_iff (hC.re_inner_nonneg_right x) (hp.re_inner_nonneg_right x)).mp
  change ENNReal.ofReal (inner ℂ x (C x)).re =
    ENNReal.ofReal (inner ℂ x (weightedConditionalRight η hη (weightedRoot 2 σ hσ)
      (weightedConditional θ hθ (weightedRoot 2 τD hD) B) x)).re
  rw [hCe,inversePower_root_four,weightedConditionalRight_twopass_form η θ hη hθ σ τD hσ hD B hB
    (basisMoment b w) hBe]
  rfl
end

section
open QuantumTrace TensorLp

theorem output_logarithm_representation {n : ℕ} (ρ : State n) {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op)
    {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) :
    ∃ B : Fock n →L[ℂ] Fock n, B.IsPositive ∧ ∀ x,
      ENNReal.ofReal (inner ℂ x (B x)).re =
        basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j)))
          (inversePower rootNumberWeight rootNumberWeight_one_le 4 x) := by
  let V : Unit → Fock n →L[ℂ] Fock n := fun _ => 1
  have hV : ∀ x : Fock n, HasSum (fun i => ‖V i x‖^2) (‖x‖^2) := by
    intro x
    simpa only [V,one_apply_eq_self,Finset.univ_unique,Finset.sum_singleton]
      using (hasSum_fintype (fun i : Unit => ‖V i x‖^2))
  have hE : ∀ x : Fock n,
      (∑' i, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (V i x)) ≤
        vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x+
          ENNReal.ofReal 0*ENNReal.ofReal (‖x‖^2) := by
    intro x
    simp only [V,one_apply_eq_self,tsum_fintype,Fintype.sum_unique,ENNReal.ofReal_zero,zero_mul,add_zero,le_refl]
  obtain ⟨C,hC,hCe⟩ := logarithmic_slice_representation ρ hr hκ hκ1 hle b p hp hs he
    V 0 le_rfl hV hE
  let R := inversePower (rootNumberWeight (n:=n)) rootNumberWeight_one_le 3
  have hRa : R.adjoint=R := inversePower_adjoint _ _ _
  have hCR : (R*C*R).IsPositive := by
    simpa only [hRa, ← ContinuousLinearMap.mul_def, mul_assoc] using hC.adjoint_conj R
  refine ⟨R*C*R,hCR,fun x => ?_⟩
  have hquad : inner ℂ x ((R*C*R) x)=inner ℂ (R x) (C (R x)) := by
    change inner ℂ x (R (C (R x)))=_
    exact ((inversePower_positive rootNumberWeight rootNumberWeight_one_le 3).isSymmetric
      x (C (R x))).symm
  rw [hquad,hCe,energyInverse_mul_three]
  simp only [sliceMoment,V,one_apply_eq_self,tsum_fintype,Fintype.sum_unique]
end

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)

theorem exact_physical_first_logarithmic_identity {J : Type*}
    (R : Regularization n) (σ : State n) (hσ : FiniteMoment 4 σ) (hD : FiniteMoment 4 R.τD)
    (τ : State n) {r δ : ℝ} (hr : 0<r) (hδ : 0<δ) (hδ1 : δ≤1)
    (hle : (δ:ℂ) • (thermalState n r hr).op ≤ τ.op)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀j, 0<p j) (hs : HasSum p 1)
    (he : ∀j, τ.op (b j)=(p j:ℂ) • b j)
    {α β : ℝ} (hα : 0≤α) (hβ : 0≤β)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive)
    (hBe : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=
      basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x))
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (G.B x)).re = ENNReal.ofReal α*
      sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j)))
        (R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hσ)).V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x)) :
    ∃ D : Fock n →L[ℂ] Fock n, D.IsPositive ∧
      (∀ x, ENNReal.ofReal (inner ℂ x (D x)).re =
        numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
      G.quarticLogarithm = (k:ℂ) • (1 : Fock n →L[ℂ] Fock n)+
        (α:ℂ) • (weightedConditional R.η R.hη (weightedRoot 2 σ hσ)
          (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩
            (weightedRoot 2 R.τD hD) B))+(β:ℂ) • D+
        (Real.log (heatPartition G.eigenval):ℂ) •
          (inversePower rootNumberWeight rootNumberWeight_one_le 4 *
            inversePower rootNumberWeight rootNumberWeight_one_le 4) := by
  obtain ⟨C,D,hC,hD',hCe,hDe,hid⟩ := G.exact_logarithmic_identity
    (R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hσ)) τ hr hδ hδ1 hle
      b p hp hs he hα hβ hform
  have hphysical := spectral_physical_twopass_identification R.η (1-R.δ) R.hη
    ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩ σ R.τD hσ hD b
      (fun j => ENNReal.ofReal (-Real.log (p j))) B C hB hC hBe hCe
  exact ⟨D,hD',hDe,by simpa only [hphysical] using hid⟩

theorem exact_physical_second_logarithmic_identity {J : Type*}
    (R : Regularization n) (σ : State n) (hσ : FiniteMoment 4 σ) (hD : FiniteMoment 4 R.τD)
    (τ : State n) {r δ : ℝ} (hr : 0<r) (hδ : 0<δ) (hδ1 : δ≤1)
    (hle : (δ:ℂ) • (thermalState n r hr).op ≤ τ.op)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀j, 0<p j) (hs : HasSum p 1)
    (he : ∀j, τ.op (b j)=(p j:ℂ) • b j)
    {α β : ℝ} (hα : 0≤α) (hβ : 0≤β)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive)
    (hBe : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=
      basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x))
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (G.B x)).re = ENNReal.ofReal α*
      sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j)))
        (R.secondFlow σ (finiteMoment_finiteEnergy (by norm_num) hσ)).V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x)) :
    ∃ D : Fock n →L[ℂ] Fock n, D.IsPositive ∧
      (∀ x, ENNReal.ofReal (inner ℂ x (D x)).re =
        numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
      G.quarticLogarithm = (k:ℂ) • (1 : Fock n →L[ℂ] Fock n)+
        (α:ℂ) • (weightedConditionalRight R.η R.hη (weightedRoot 2 σ hσ)
          (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩
            (weightedRoot 2 R.τD hD) B))+(β:ℂ) • D+
        (Real.log (heatPartition G.eigenval):ℂ) •
          (inversePower rootNumberWeight rootNumberWeight_one_le 4 *
            inversePower rootNumberWeight rootNumberWeight_one_le 4) := by
  obtain ⟨C,D,hC,hD',hCe,hDe,hid⟩ := G.exact_logarithmic_identity
    (R.secondFlow σ (finiteMoment_finiteEnergy (by norm_num) hσ)) τ hr hδ hδ1 hle
      b p hp hs he hα hβ hform
  have hphysical := spectral_physical_right_twopass_identification R.η (1-R.δ) R.hη
    ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩ σ R.τD hσ hD b
      (fun j => ENNReal.ofReal (-Real.log (p j))) B C hB hC hBe hCe
  exact ⟨D,hD',hDe,by simpa only [hphysical] using hid⟩
end GibbsData
end

namespace Regularization
open QuantumTrace
variable {n : ℕ} (R : Regularization n)

theorem minimum_centered_gibbs_data (ρ σ : State n) (hmρ : FiniteMoment 4 ρ) (hmσ : FiniteMoment 4 σ)
    {r : ℝ} (hr : 0 < r) (hτ : R.τ0 = thermalState n r hr) (hκ : 0 < R.κ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' → R.objective ρ σ ≤ R.objective ρ' σ') :
    ∃ (J : Type) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ),
      (∀ j, 0 < p j) ∧ HasSum p 1 ∧ (∀ j, (R.output ρ σ).op (b j) = (p j : ℂ) • b j) ∧
      ∃ (G1 : GibbsData n (R.ζ/R.a1) ρ) (G2 : GibbsData n (R.ζ/R.a2) σ),
        (∀ x, ENNReal.ofReal (inner ℂ x (G1.B x)).re =
          ENNReal.ofReal (R.c*(1-R.κ)/R.a1)*sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j)))
            (R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hmσ)).V (energyInverse n x)+
          ENNReal.ofReal (R.b1/R.a1)*numberVectorMoment (energyInverse n x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (G2.B x)).re =
          ENNReal.ofReal (R.c*(1-R.κ)/R.a2)*sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j)))
            (R.secondFlow ρ (finiteMoment_finiteEnergy (by norm_num) hmρ)).V (energyInverse n x)+
          ENNReal.ofReal (R.b2/R.a2)*numberVectorMoment (energyInverse n x)) ∧
        (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace b p →
          (1-R.κ)^2*BKM.quadratic G1.basis (gibbsWeight G1.eigenval)
            (BKM.center G1.basis (gibbsWeight G1.eigenval)
              ((R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hmσ)).dual Z)) ≤
            (R.a1/R.c)*BKM.quadratic b p Z) ∧
        (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace b p →
          (1-R.κ)^2*BKM.quadratic G2.basis (gibbsWeight G2.eigenval)
            (BKM.center G2.basis (gibbsWeight G2.eigenval)
              ((R.secondFlow ρ (finiteMoment_finiteEnergy (by norm_num) hmρ)).dual Z)) ≤
            (R.a2/R.c)*BKM.quadratic b p Z) := by
  classical
  have hle : (R.κ : ℂ) • (thermalState n r hr).op ≤ (R.output ρ σ).op := by
    rw [← hτ]
    exact mixture_replacement_le R.κ R.hκ (R.rawOutput ρ σ) R.τ0
  obtain ⟨J,b,p,hp,hs,he⟩ := exists_faithful_eigenbasis_of_thermal_le (R.output ρ σ) hr hκ hle
  have hmin1 (ρ' : State n) (hmρ' : FiniteMoment 4 ρ') := hmin ρ' σ hmρ' hmσ
  have hmin2 (σ' : State n) (hmσ' : FiniteMoment 4 σ') := hmin ρ σ' hmρ hmσ'
  obtain ⟨G1,hG1,hh1⟩ := minimum_centered_hessian_data
    (R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hmσ)) R.τ0 hr hτ R.κ R.hκ hκ
    R.c R.a1 R.b1 R.ζ R.hc R.ha1 R.hb1.le R.hζ ρ hmρ b p hp hs he (by
      intro ρ' hmρ'
      have h := hmin1 ρ' hmρ'
      dsimp only [objective] at h
      change R.c*entropy (R.output ρ σ)-R.a1*entropy ρ+R.b1*energy ρ+R.ζ*numberMoment 4 ρ ≤
        R.c*entropy (R.output ρ' σ)-R.a1*entropy ρ'+R.b1*energy ρ'+R.ζ*numberMoment 4 ρ'
      linarith)
  obtain ⟨G2,hG2,hh2⟩ := minimum_centered_hessian_data
    (R.secondFlow ρ (finiteMoment_finiteEnergy (by norm_num) hmρ)) R.τ0 hr hτ R.κ R.hκ hκ
    R.c R.a2 R.b2 R.ζ R.hc R.ha2 R.hb2.le R.hζ σ hmσ b p hp hs he (by
      intro σ' hmσ'
      have h := hmin2 σ' hmσ'
      dsimp only [objective] at h
      change R.c*entropy (R.output ρ σ)-R.a2*entropy σ+R.b2*energy σ+R.ζ*numberMoment 4 σ ≤
        R.c*entropy (R.output ρ σ')-R.a2*entropy σ'+R.b2*energy σ'+R.ζ*numberMoment 4 σ'
      linarith)
  exact ⟨J,b,p,hp,hs,he,G1,G2,hG1,hG2,hh1,hh2⟩

end Regularization

open QuantumTrace Annihilation BeamLadder TensorLp
namespace Regularization
variable {n : ℕ} (R : Regularization n)

theorem minimum_physical_log_data (ρ σ : State n) (hmρ : FiniteMoment 4 ρ)
    (hmσ : FiniteMoment 4 σ) (hmD : FiniteMoment 4 R.τD)
    {r : ℝ} (hr : 0 < r) (hτ : R.τ0 = thermalState n r hr) (hκ : 0 < R.κ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' → R.objective ρ σ ≤ R.objective ρ' σ') :
    ∃ (J : Type) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ),
      (∀ j, 0 < p j) ∧ HasSum p 1 ∧ (∀ j, (R.output ρ σ).op (b j) = (p j : ℂ) • b j) ∧
      ∃ (G1 : GibbsData n (R.ζ/R.a1) ρ) (G2 : GibbsData n (R.ζ/R.a2) σ)
        (B D1 D2 : Fock n →L[ℂ] Fock n), B.IsPositive ∧ D1.IsPositive ∧ D2.IsPositive ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=
          basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (D1 x)).re=
          numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (D2 x)).re=
          numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
        (G1.quarticLogarithm = ((R.ζ/R.a1:ℝ):ℂ) • (1 : Fock n →L[ℂ] Fock n)+
          ((R.c*(1-R.κ)/R.a1:ℝ):ℂ) •
            (weightedConditional R.η R.hη (weightedRoot 2 σ hmσ)
              (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
                (weightedRoot 2 R.τD hmD) B))+
          ((R.b1/R.a1:ℝ):ℂ) • D1+(Real.log (heatPartition G1.eigenval):ℂ) •
            (inversePower rootNumberWeight rootNumberWeight_one_le 4 *
              inversePower rootNumberWeight rootNumberWeight_one_le 4)) ∧
        (G2.quarticLogarithm = ((R.ζ/R.a2:ℝ):ℂ) • (1 : Fock n →L[ℂ] Fock n)+
          ((R.c*(1-R.κ)/R.a2:ℝ):ℂ) •
            (weightedConditionalRight R.η R.hη (weightedRoot 2 ρ hmρ)
              (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
                (weightedRoot 2 R.τD hmD) B))+
          ((R.b2/R.a2:ℝ):ℂ) • D2+(Real.log (heatPartition G2.eigenval):ℂ) •
            (inversePower rootNumberWeight rootNumberWeight_one_le 4 *
              inversePower rootNumberWeight rootNumberWeight_one_le 4)) ∧
        (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace b p →
          (1-R.κ)^2*BKM.quadratic G1.basis (gibbsWeight G1.eigenval)
            (BKM.center G1.basis (gibbsWeight G1.eigenval)
              ((R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hmσ)).dual Z)) ≤
            (R.a1/R.c)*BKM.quadratic b p Z) ∧
        (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace b p →
          (1-R.κ)^2*BKM.quadratic G2.basis (gibbsWeight G2.eigenval)
            (BKM.center G2.basis (gibbsWeight G2.eigenval)
              ((R.secondFlow ρ (finiteMoment_finiteEnergy (by norm_num) hmρ)).dual Z)) ≤
            (R.a2/R.c)*BKM.quadratic b p Z) := by
  obtain ⟨J,b,p,hp,hs,he,G1,G2,hf1,hf2,hh1,hh2⟩ :=
    R.minimum_centered_gibbs_data ρ σ hmρ hmσ hr hτ hκ hmin
  have hle : (R.κ : ℂ) • (thermalState n r hr).op ≤ (R.output ρ σ).op := by
    rw [← hτ]
    exact mixture_replacement_le R.κ R.hκ (R.rawOutput ρ σ) R.τ0
  obtain ⟨B,hB,hBe⟩ := output_logarithm_representation (R.output ρ σ) hr hκ R.hκ.2 hle b p hp hs he
  have hBe' (x : Fock n) : ENNReal.ofReal (inner ℂ x (B x)).re=
      basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x) := by
    simpa only [inversePower_root_four] using hBe x
  have hα1 : 0 ≤ R.c*(1-R.κ)/R.a1 :=
    div_nonneg (mul_nonneg R.hc.le (sub_nonneg.mpr R.hκ.2)) R.ha1.le
  have hα2 : 0 ≤ R.c*(1-R.κ)/R.a2 :=
    div_nonneg (mul_nonneg R.hc.le (sub_nonneg.mpr R.hκ.2)) R.ha2.le
  obtain ⟨D1,hD1,heD1,hid1⟩ := G1.exact_physical_first_logarithmic_identity R σ hmσ hmD
    (R.output ρ σ) hr hκ R.hκ.2 hle b p hp hs he hα1
      (div_nonneg R.hb1.le R.ha1.le) B hB hBe' hf1
  obtain ⟨D2,hD2,heD2,hid2⟩ := G2.exact_physical_second_logarithmic_identity R ρ hmρ hmD
    (R.output ρ σ) hr hκ R.hκ.2 hle b p hp hs he hα2
      (div_nonneg R.hb2.le R.ha2.le) B hB hBe' hf2
  exact ⟨J,b,p,hp,hs,he,G1,G2,B,D1,D2,hB,hD1,hD2,hBe',heD1,heD2,hid1,hid2,hh1,hh2⟩
end Regularization
end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ} {I : Type*}

theorem pairing_add (r : ℝ) (x : I → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (A B : Fock n →L[ℂ] Fock n) :
    pairing r x (A+B)=pairing r x A+pairing r x B := by
  apply (pairing_hasSum (numberBasis n) r x hx (A+B)).unique
  convert! (pairing_hasSum (numberBasis n) r x hx A).add
    (pairing_hasSum (numberBasis n) r x hx B) using 1
  ext k
  simp only [add_apply,inner_add_right]

theorem pairing_smul (r : ℝ) (x : I → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (c : ℂ) (A : Fock n →L[ℂ] Fock n) :
    pairing r x (c • A)=c*pairing r x A := by
  apply (pairing_hasSum (numberBasis n) r x hx (c • A)).unique
  convert! (pairing_hasSum (numberBasis n) r x hx A).mul_left c using 1
  ext k
  simp only [smul_apply,inner_smul_right]

theorem pairing_scalar_inverse (r : ℝ) (x : I → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (c : ℂ) :
    pairing r x (c • (inversePower rootNumberWeight rootNumberWeight_one_le 4 *
      inversePower rootNumberWeight rootNumberWeight_one_le 4))=0 := by
  rw [pairing_smul r x hx,inversePower_root_four]
  change c*pairing r x (inverseWeight 2 ∘L inverseWeight 2)=0
  rw [← inverseWeight_add,pairing_inverse_zero,mul_zero]
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

private theorem pairing_balance_algebra (a1 a2 c k b1 b2 t l1 l2 w1 w2 s1 s2 d1 d2 : ℂ)
    (ha1 : a1 ≠ 0) (ha2 : a2 ≠ 0)
    (h1 : l1=k/a1*w1+c*t/a1*s1+b1/a1*d1)
    (h2 : l2=k/a2*w2+c*t/a2*s2+b2/a2*d2) :
    a1*l1+a2*l2=c*t*(s1+s2)+b1*d1+b2*d2+k*(w1+w2) := by
  rw [h1,h2]
  field_simp [ha1,ha2]; ring

theorem minimum_physical_pairing_balance (ρ σ : State n) (hmρ : FiniteMoment 4 ρ)
    (hmσ : FiniteMoment 4 σ) (hmD : FiniteMoment 4 R.τD)
    {r : ℝ} (hr : 0 < r) (hτ : R.τ0 = thermalState n r hr) (hκ : 0 < R.κ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' → R.objective ρ σ ≤ R.objective ρ' σ') :
    ∃ (J : Type) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ),
      (∀ j, 0 < p j) ∧ HasSum p 1 ∧ (∀ j, (R.output ρ σ).op (b j) = (p j : ℂ) • b j) ∧
      ∃ (G1 : GibbsData n (R.ζ/R.a1) ρ) (G2 : GibbsData n (R.ζ/R.a2) σ)
        (B D1 D2 : Fock n →L[ℂ] Fock n), B.IsPositive ∧ D1.IsPositive ∧ D2.IsPositive ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=
          basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (D1 x)).re=
          numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (D2 x)).re=
          numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
        (∀ (s1 s2 : ℝ) (X : WeightedColumns ρ) (Y : WeightedColumns σ),
          (R.a1:ℂ)*WeightedGenerator.pairing s1 X.vector G1.quarticLogarithm+
          (R.a2:ℂ)*WeightedGenerator.pairing s2 Y.vector G2.quarticLogarithm=
          (R.c:ℂ)*((1-R.κ:ℝ):ℂ)*
            (WeightedGenerator.pairing s1 X.vector
              (weightedConditional R.η R.hη (weightedRoot 2 σ hmσ)
                (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
                  (weightedRoot 2 R.τD hmD) B))+
             WeightedGenerator.pairing s2 Y.vector
              (weightedConditionalRight R.η R.hη (weightedRoot 2 ρ hmρ)
                (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
                  (weightedRoot 2 R.τD hmD) B)))+
          (R.b1:ℂ)*WeightedGenerator.pairing s1 X.vector D1+
          (R.b2:ℂ)*WeightedGenerator.pairing s2 Y.vector D2+
          (R.ζ:ℂ)*(WeightedGenerator.pairing s1 X.vector (1 : Fock n →L[ℂ] Fock n)+
            WeightedGenerator.pairing s2 Y.vector (1 : Fock n →L[ℂ] Fock n))) ∧
        (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace b p →
          (1-R.κ)^2*BKM.quadratic G1.basis (gibbsWeight G1.eigenval)
            (BKM.center G1.basis (gibbsWeight G1.eigenval)
              ((R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hmσ)).dual Z)) ≤
            (R.a1/R.c)*BKM.quadratic b p Z) ∧
        (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace b p →
          (1-R.κ)^2*BKM.quadratic G2.basis (gibbsWeight G2.eigenval)
            (BKM.center G2.basis (gibbsWeight G2.eigenval)
              ((R.secondFlow ρ (finiteMoment_finiteEnergy (by norm_num) hmρ)).dual Z)) ≤
            (R.a2/R.c)*BKM.quadratic b p Z) := by
  obtain ⟨J,b,p,hp,hs,he,G1,G2,B,D1,D2,hB,hD1,hD2,hBe,heD1,heD2,hid1,hid2,hh1,hh2⟩ :=
    R.minimum_physical_log_data ρ σ hmρ hmσ hmD hr hτ hκ hmin
  refine ⟨J,b,p,hp,hs,he,G1,G2,B,D1,D2,hB,hD1,hD2,hBe,heD1,heD2,?_,hh1,hh2⟩
  intro s1 s2 X Y
  have he1 := congrArg (WeightedGenerator.pairing s1 X.vector) hid1
  have he2 := congrArg (WeightedGenerator.pairing s2 Y.vector) hid2
  simp only [WeightedGenerator.pairing_add s1 X.vector X.summable,
    WeightedGenerator.pairing_scalar_inverse s1 X.vector X.summable,
    WeightedGenerator.pairing_smul s1 X.vector X.summable,add_zero,
    Complex.ofReal_div,Complex.ofReal_mul] at he1
  simp only [WeightedGenerator.pairing_add s2 Y.vector Y.summable,
    WeightedGenerator.pairing_scalar_inverse s2 Y.vector Y.summable,
    WeightedGenerator.pairing_smul s2 Y.vector Y.summable,add_zero,
    Complex.ofReal_div,Complex.ofReal_mul] at he2
  apply pairing_balance_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he1 he2
  · exact_mod_cast R.ha1.ne'
  · exact_mod_cast R.ha2.ne'
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

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.Regularization
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
open QuantumTrace Annihilation BeamLadder TensorLp


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.Regularization.minimum_physical_pairing_balance := @_root_.OAI.EntropyPhotonNumber.Regularization.minimum_physical_pairing_balance
