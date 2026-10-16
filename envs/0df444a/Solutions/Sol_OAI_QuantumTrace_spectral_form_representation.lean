-- Prove2me | solution 1 for OAI.QuantumTrace.spectral_form_representation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:24:26.167451+00:00
-- url     : https://prove2.me/submissions/5c2e242a-4fff-4fe9-918e-2cfd805f4559

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/SpectralLog.lean:L110-L153
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.spectral_form_representation. The node keeps its source
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

theorem gram_positive (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) :
    (gram f hs C hC hb).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self _

theorem gram_quadratic (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) (x : E) :
    (inner ℂ x (gram f hs C hC hb x)).re = ∑' i, ‖f i x‖^2 := by
  exact ((continuousMap f hs C hC hb).apply_norm_sq_eq_inner_adjoint_right x).symm.trans
    (vector_norm_sq f hs x)

end SquareAnalysis

namespace QuantumTrace
open scoped ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

omit [CompleteSpace E] in
theorem logCoordinates_square (b : HilbertBasis J ℂ E) (c : J → ℝ) (hc : ∀ j, 0≤c j)
    (V : E →L[ℂ] E) (j : J) (x : E) :
    ‖logCoordinates b c V j x‖^2=c j*‖inner ℂ (b j) (V x)‖^2 := by
  change ‖(Real.sqrt (c j):ℂ)*inner ℂ (b j) (V x)‖^2=_
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (hc j)]

theorem spectral_form_representation (b : HilbertBasis J ℂ E) (c : J → ℝ)
    (hc : ∀ j, 0≤c j) (V : E →L[ℂ] E) (hV : V.IsSymmetric)
    (hs : ∀ y, Summable (fun j => c j*‖inner ℂ (b j) (V y)‖^2))
    {C : ℝ} (hC : 0≤C)
    (hb : ∀ y, (∑' j, c j*‖inner ℂ (b j) (V y)‖^2)≤C*‖y‖^2) :
    ∃ B : E →L[ℂ] E, B.IsPositive ∧
      (∀ y, HasSum (fun j => c j*‖inner ℂ (b j) (V y)‖^2) (inner ℂ y (B y)).re) ∧
      ∀ (j : J) (y : E) (z : ℂ), V y=z • b j → B y=(c j:ℂ) • V (z • b j) := by
  classical
  let f := logCoordinates b c V
  have hf (y : E) : Summable (fun j => ‖f j y‖^2) := by
    simpa only [f,logCoordinates_square b c hc] using hs y
  have hfB (y : E) : (∑' j, ‖f j y‖^2)≤C*‖y‖^2 := by
    simpa only [f,logCoordinates_square b c hc] using hb y
  let A := SquareAnalysis.continuousMap f hf C hC hfB
  refine ⟨SquareAnalysis.gram f hf C hC hfB, SquareAnalysis.gram_positive f hf C hC hfB, ?_, ?_⟩
  · intro y
    rw [SquareAnalysis.gram_quadratic]
    simpa only [f,logCoordinates_square b c hc] using (hf y).hasSum
  · intro j y z hy
    have hAy : A y=((Real.sqrt (c j):ℂ)*z) • (lp.single (E := fun _ : J => ℂ) 2 j (1:ℂ)) := by
      apply lp.ext
      funext i
      change (Real.sqrt (c i):ℂ)*inner ℂ (b i) (V y)=_
      rw [hy,inner_smul_right]
      by_cases hi : i=j
      · subst i
        simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one, lp.single_apply]
      · have hii : inner ℂ (b i) (b j)=0 := b.orthonormal.inner_eq_zero hi
        simp [hii,lp.single_apply,Ne.symm hi]
    apply ext_inner_left ℂ
    intro x
    change inner ℂ x (A.adjoint (A y))=inner ℂ x ((c j:ℂ) • V (z • b j))
    rw [A.adjoint_inner_right,hAy,inner_smul_right,lp.inner_single_right]
    simp only [RCLike.inner_apply,one_mul]
    change ((Real.sqrt (c j):ℂ)*z)*conj (f j x)=_
    change ((Real.sqrt (c j):ℂ)*z)*conj ((Real.sqrt (c j):ℂ)*inner ℂ (b j) (V x))=_
    rw [map_mul,Complex.conj_ofReal,inner_smul_right,map_smul,inner_smul_right]
    have he : inner ℂ x (V (b j))=conj (inner ℂ (b j) (V x)) := by
      rw [← inner_conj_symm]
      exact congrArg conj (hV (b j) x)
    rw [he]
    have hsqrt : (Real.sqrt (c j):ℂ)^2=(c j:ℂ) := by exact_mod_cast Real.sq_sqrt (hc j)
    linear_combination (z*conj (inner ℂ (b j) (V x)))*hsqrt
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

-- ---- platform node ----
open OAI OAI.QuantumTrace
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
open scoped ComplexConjugate


theorem solution : type_of% @_root_.OAI.QuantumTrace.spectral_form_representation := @_root_.OAI.QuantumTrace.spectral_form_representation
