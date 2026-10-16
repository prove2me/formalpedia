-- Prove2me | solution 1 for OAI.Annihilation.weighted_trace_ext
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:40:56.122167+00:00
-- url     : https://prove2.me/submissions/2df565a6-b145-4340-9833-fa149795e04c

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/BeamForms.lean:L1331-L1353
-- (upload_full_project.md Phase 4): solution for node OAI.Annihilation.weighted_trace_ext. The node keeps its source
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

end BeamLadder

namespace EnsemblePullback

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I : Type*}

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

theorem rankOne_trace (b : HilbertBasis J ℂ E) (A : E →L[ℂ] E) (x y : E) :
    HasSum (fun k => inner ℂ (b k) ((InnerProductSpace.rankOne ℂ x y) (A (b k))))
      (inner ℂ y (A x)) := by
  convert! b.hasSum_inner_mul_inner (A.adjoint y) x using 1
  · ext k
    simp only [InnerProductSpace.rankOne_apply, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_left]
  · rw [ContinuousLinearMap.adjoint_inner_left]

variable {I : Type*}
end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

theorem inverseWeight_rankOne_range (m : ℕ) (k : NumberIndex n) :
    ∃ v : Fock n, inverseWeight m v=numberKet k := by
  refine ⟨lp.single 2 k ((numberWeight k:ℂ)^m), ?_⟩
  have hh := WeightedShift.pullCLM_single id Function.injective_id
    (fun a : NumberIndex n => ((numberWeight a:ℂ)^m)⁻¹) 1 (by norm_num)
    (coefficient_inverse_bound m) k ((numberWeight k:ℂ)^m)
  change inverseWeight m (lp.single 2 k ((numberWeight k:ℂ)^m))=_ at hh
  rw [hh]
  have hw : (numberWeight k:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le k] : numberWeight k≠0)
  simp only [inv_mul_cancel₀ (pow_ne_zero m hw)]
  rfl

theorem inverseWeight_rankOne (m : ℕ) (x y : Fock n) :
    inverseWeight m ∘L InnerProductSpace.rankOne ℂ x y ∘L inverseWeight m =
      InnerProductSpace.rankOne ℂ (inverseWeight m x) (inverseWeight m y) := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply,InnerProductSpace.rankOne_apply,map_smul]
  exact congrArg (fun a : ℂ => a • inverseWeight m x)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (inverseWeight_selfAdjoint m) y z).symm

theorem weighted_trace_ext {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (A Q : Fock n →L[ℂ] Fock n)
    (f g : (Fock n →L[ℂ] Fock n) → ℂ)
    (hf : ∀ Z, HasSum (fun k => inner ℂ (b k) (Z (A (b k)))) (f Z))
    (hg : ∀ Z, HasSum (fun k => inner ℂ (b k) (Z (Q (b k)))) (g Z))
    (h : ∀ Z, f (inverseWeight 2 ∘L Z ∘L inverseWeight 2)=
      g (inverseWeight 2 ∘L Z ∘L inverseWeight 2)) : ∀ Z, f Z=g Z := by
  have he : A=Q := by
    apply entry_ext
    intro k l
    obtain ⟨x,hx⟩ := inverseWeight_rankOne_range 2 l
    obtain ⟨y,hy⟩ := inverseWeight_rankOne_range 2 k
    have hh := h (InnerProductSpace.rankOne ℂ x y)
    rw [inverseWeight_rankOne,hx,hy] at hh
    have hA := (hf (InnerProductSpace.rankOne ℂ (numberKet l) (numberKet k))).unique
      (CrossEnsemble.rankOne_trace b A (numberKet l) (numberKet k))
    have hQ := (hg (InnerProductSpace.rankOne ℂ (numberKet l) (numberKet k))).unique
      (CrossEnsemble.rankOne_trace b Q (numberKet l) (numberKet k))
    exact hA.symm.trans (hh.trans hQ)
  intro Z
  apply (hf Z).unique
  rw [he]
  exact hg Z
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

-- ---- platform node ----
open OAI OAI.Annihilation
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
open EntropyPhotonNumber QuantumTrace


theorem solution : type_of% @_root_.OAI.Annihilation.weighted_trace_ext := @_root_.OAI.Annihilation.weighted_trace_ext
