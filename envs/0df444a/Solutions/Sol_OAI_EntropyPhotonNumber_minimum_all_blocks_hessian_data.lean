-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.minimum_all_blocks_hessian_data
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:59:29.435979+00:00
-- url     : https://prove2.me/submissions/f8b1fab9-b124-4bab-9d40-7905cf4a42df

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean:L2679-L2746
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.minimum_all_blocks_hessian_data. The node keeps its source
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
import Theorems.Thm_OAI_BKM_finite_hessian_to_variance
import Theorems.Thm_OAI_EntropyPhotonNumber_GibbsData_crossEntropy_hamiltonian
import Theorems.Thm_OAI_EntropyPhotonNumber_blockState_operator
import Theorems.Thm_OAI_EntropyPhotonNumber_block_crossEntropy
import Theorems.Thm_OAI_EntropyPhotonNumber_crossEntropy_finite
import Theorems.Thm_OAI_EntropyPhotonNumber_flow_minimum_gibbs
import Theorems.Thm_OAI_FiniteBlock_exp_spectral
import Theorems.Thm_OAI_QuantumCalculus_log_partition_expansion
import Theorems.Thm_OAI_QuantumCalculus_matrix_duhamel_hessian
import Theorems.Thm_OAI_QuantumTrace_cfc_apply_eigenvector
import Theorems.Thm_OAI_QuantumTrace_entropy_summable_and_le_crossEntropy
import Theorems.Thm_OAI_QuantumTrace_exists_positive_eigenbasis
import Theorems.Thm_OAI_QuantumTrace_hasSum_trace_basis
import Theorems.Thm_OAI_QuantumTrace_quantum_klein
import Theorems.Thm_OAI_TraceEnsemble_hasSum_expectation_basis

-- ---- from OAI.Analysis.QuantumTrace.Basic ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
private theorem CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab

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

theorem quadratic_le_trace_mul_norm_sq (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) (x : E) :
    (inner ℂ x (T x)).re ≤ τ * ‖x‖ ^ 2 := by
  let S := CFC.sqrt T
  have hs : S.IsSymmetric :=
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg T)).isSymmetric
  have ht' : HasSum (fun i => ‖S (b i)‖ ^ 2) τ := by
    simpa only [sqrt_inner_eq hT] using ht
  rw [sqrt_inner_eq hT, ← (basis_hasSum_norm_sq b (S x)).tsum_eq,
    ← ht'.tsum_eq, ← tsum_mul_right]
  apply Summable.tsum_le_tsum
  · intro i
    have he : inner ℂ (b i) (S x) = inner ℂ (S (b i)) x := (hs (b i) x).symm
    rw [he]
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) (S (b i)) x) 2
  · exact (basis_hasSum_norm_sq b (S x)).summable
  · exact ht'.summable.mul_right _

theorem operator_le_trace_smul_id (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) :
    T ≤ (τ : ℂ) • ContinuousLinearMap.id ℂ E := by
  rw [ContinuousLinearMap.le_def]
  refine ⟨?_, ?_⟩
  · exact (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id).sub hT.isSymmetric
  · intro x
    change 0 ≤ (inner ℂ (((τ : ℂ) • ContinuousLinearMap.id ℂ E - T) x) x).re
    rw [sub_apply, smul_apply, ContinuousLinearMap.id_apply, inner_sub_left, inner_smul_left,
      hT.inner_left_eq_inner_right x x]
    simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using
      sub_nonneg.mpr (quadratic_le_trace_mul_norm_sq b hT ht x)

theorem norm_le_trace (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) : ‖T‖ ≤ τ := by
  have hn : 0 ≤ τ := ht.nonneg (fun i => hT.re_inner_nonneg_right (b i))
  have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (operator_le_trace_smul_id b hT ht) ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hT)
  apply h.trans
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  exact mul_le_of_le_one_right hn ContinuousLinearMap.norm_id_le

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

theorem entropyOperator_eq_complex {T : E →L[ℂ] E} (hs : T.IsSymmetric) :
    entropyOperator T = cfc (fun z : ℂ => (-(z.re * Real.log z.re) : ℂ)) T := by
  rw [entropyOperator, cfc_real_eq_complex Real.negMulLog hs.isSelfAdjoint]
  congr 1
  funext z
  simp [Real.negMulLog_def]

theorem entropyOperator_positive {T : E →L[ℂ] E} (hp : T.IsPositive) (hn : ‖T‖ ≤ 1) :
    (entropyOperator T).IsPositive := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    have : entropyOperator T = 0 := Subsingleton.elim _ _
    rw [this]
    exact isPositive_zero
  | inr h =>
    apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
    exact cfc_nonneg (fun x hx => Real.negMulLog_nonneg
    (spectrum_nonneg_of_nonneg ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp) hx)
    ((Real.le_norm_self _).trans ((spectrum.norm_le_norm_of_mem hx).trans hn)))

end

section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {ι : Type*}

theorem entropy_jensen_hasSum {p w : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hw : ∀ i, 0 ≤ w i) (hw1 : HasSum w 1) {a s : ℝ}
    (ha : HasSum (fun i => w i * p i) a)
    (hs : HasSum (fun i => w i * Real.negMulLog (p i)) s) :
    s ≤ Real.negMulLog a := by
  apply le_of_tendsto_of_tendsto hs (Real.continuous_negMulLog.tendsto a |>.comp ha)
  apply Filter.Eventually.of_forall
  intro t
  have ht : ∑ i ∈ t, w i ≤ 1 := by
    rw [← hw1.tsum_eq]
    exact hw1.summable.sum_le_tsum t (fun i _ => hw i)
  have hf := Real.concaveOn_negMulLog.map_add_sum_le
    (t := t) (w := w) (p := p) (v := 1 - ∑ i ∈ t, w i) (q := 0)
    (fun i _ => hw i) (by ring) (fun i _ => hp i) (sub_nonneg.mpr ht) (by simp)
  simpa [Function.comp_def] using hf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem entropyOperator_apply_eigenvector {T : E →L[ℂ] E} (hs : T.IsSymmetric)
    {x : E} {p : ℝ} (he : T x = (p : ℂ) • x) :
    entropyOperator T x = (Real.negMulLog p : ℂ) • x := by
  rw [entropyOperator_eq_complex hs]
  have hf : Continuous (fun z : ℂ => (Real.negMulLog z.re : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_negMulLog.comp Complex.continuous_re)
  simpa [Real.negMulLog_def] using cfc_apply_eigenvector hs he _ hf.continuousOn

theorem entropyOperator_quadratic_le (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ)
    (x : E) (hx : ‖x‖ = 1) :
    (inner ℂ x (entropyOperator T x)).re ≤ Real.negMulLog (inner ℂ x (T x)).re := by
  obtain ⟨J, c, p, hpn, _, he⟩ := exists_positive_eigenbasis b hp ht
  apply entropy_jensen_hasSum hpn (fun j => sq_nonneg ‖inner ℂ (c j) x‖)
  · simpa only [hx, one_pow] using basis_hasSum_norm_sq c x
  · simpa only [mul_comm] using hasSum_quadratic_eigenbasis c T p he x
  · simpa only [mul_comm] using hasSum_quadratic_eigenbasis c (entropyOperator T)
      (fun j => Real.negMulLog (p j)) (fun j => entropyOperator_apply_eigenvector hp.isSymmetric (he j)) x

end

section

theorem log_thermalWeight (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin n → ℕ) :
    -Real.log (thermalWeight n r k) =
      n * Real.log (r + 1) + (∑ j, (k j : ℝ)) * Real.log ((r + 1) / r) := by
  have hr1 : 0 < r + 1 := by linarith
  rw [thermalWeight, Real.log_prod (fun _ _ => by positivity)]
  simp only [Real.log_mul (inv_ne_zero hr1.ne') (pow_ne_zero _ (div_ne_zero hr.ne' hr1.ne')),
    Real.log_inv, Real.log_pow, Real.log_div hr.ne' hr1.ne',
    Real.log_div hr1.ne' hr.ne', Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  ring

theorem summable_thermal_crossEntropy {n : ℕ} {p : (Fin n → ℕ) → ℝ}
    (hp : Summable p) (hE : Summable (fun k => (∑ j, (k j : ℝ)) * p k))
    {r : ℝ} (hr : 0 < r) :
    Summable (fun k => p k * (-Real.log (thermalWeight n r k))) := by
  have hh := (hp.mul_right (n * Real.log (r + 1))).add
    (hE.mul_right (Real.log ((r + 1) / r)))
  convert! hh using 1
  ext k
  rw [log_thermalWeight n hr k]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem entropy_summable_finite_energy {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive)
    (ht : HasSum (fun k => (inner ℂ (b k) (T (b k))).re) 1)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re)) :
    Summable (fun k => (inner ℂ (b k) (entropyOperator T (b k))).re) := by
  have hc := (entropy_summable_and_le_crossEntropy
    (fun k => (inner ℂ (b k) (T (b k))).re) (thermalWeight n 1)
    (fun k => hp.re_inner_nonneg_right (b k)) (thermalWeight_pos n zero_lt_one)
    ht (hasSum_thermalWeight n zero_lt_one)
    (summable_thermal_crossEntropy ht.summable hE zero_lt_one)).1
  have hn : ‖T‖ ≤ 1 := by
    exact norm_le_trace b hp ht
  exact Summable.of_nonneg_of_le
    (fun k => (entropyOperator_positive hp hn).re_inner_nonneg_right (b k))
    (fun k => entropyOperator_quadratic_le b hp ht (b k) (b.orthonormal.norm_eq_one k)) hc

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

omit [CompleteSpace E] in

theorem summable_expectation_norm {v : I → E} (hv : Summable (fun i => ‖v i‖^2))
    (Z : E →L[ℂ] E) : Summable (fun i => ‖inner ℂ (v i) (Z (v i))‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hv.mul_left ‖Z‖)
  intro i
  calc
    _ ≤ ‖v i‖*‖Z (v i)‖ := norm_inner_le_norm _ _
    _ ≤ ‖v i‖*(‖Z‖*‖v i‖) := mul_le_mul_of_nonneg_left (Z.le_opNorm _) (norm_nonneg _)
    _ = ‖Z‖*‖v i‖^2 := by ring

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

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

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

 theorem dual_adjoint (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) : dual V hV Z.adjoint = (dual V hV Z).adjoint := by
  ext y
  apply ext_inner_left ℂ
  intro x
  have hh := (dual_entry V hV Z y x).mapL Complex.conjCLE.toContinuousLinearEquiv.toContinuousLinearMap
  change HasSum (fun i => starRingEnd ℂ (inner ℂ (V i y) (Z (V i x))))
    (starRingEnd ℂ (inner ℂ y (dual V hV Z x))) at hh
  exact (dual_entry V hV Z.adjoint x y).unique (by
    simpa only [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm] using hh)

 theorem dual_selfAdjoint (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    {Z : H →L[ℂ] H} (hZ : IsSelfAdjoint Z) : IsSelfAdjoint (dual V hV Z) := by
  change (dual V hV Z).adjoint = _
  rw [← dual_adjoint, show Z.adjoint = Z from hZ]

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

theorem trace_one_numberBasis {n : ℕ} (ρ : State n) :
    HasSum (fun k => (inner ℂ (numberBasis n k) (ρ.op (numberBasis n k))).re) 1 := by
  simpa only [numberBasis_apply, entry] using ρ.trace_one

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

theorem state_ext {n : ℕ} {ρ σ : State n} (h : ρ.op = σ.op) : ρ = σ := by
  cases ρ; cases σ; cases h; rfl

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

theorem entropy_eq_quantumTrace {n : ℕ} (ρ : State n) :
    entropy ρ = ∑' k, (inner ℂ (numberBasis n k)
      (QuantumTrace.entropyOperator ρ.op (numberBasis n k))).re := by
  rw [QuantumTrace.entropyOperator_eq_complex ρ.positive.isSymmetric]
  simp only [entropy, entry, numberBasis_apply]

theorem entropy_summable {n : ℕ} (ρ : State n) (hρ : FiniteEnergy ρ) :
    Summable (fun k => (entry (cfc (fun z : ℂ => (-(z.re * Real.log z.re) : ℂ)) ρ.op) k k).re) := by
  have hE : Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (numberBasis n k) (ρ.op (numberBasis n k))).re) := by
    simpa only [FiniteEnergy, totalNumber, Nat.cast_sum, numberBasis_apply, entry] using hρ
  have hh := QuantumTrace.entropy_summable_finite_energy (numberBasis n) ρ.positive (trace_one_numberBasis ρ) hE
  simpa only [QuantumTrace.entropyOperator_eq_complex ρ.positive.isSymmetric, numberBasis_apply, entry] using hh

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
theorem mixture_finiteEnergy {n : ℕ} (t : ℝ) (ht : t ∈ Set.Icc 0 1) {ρ σ : State n}
    (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) : FiniteEnergy (mixture t ht ρ σ) := by
  unfold FiniteEnergy
  convert! (hρ.mul_left t).add (hσ.mul_left (1-t)) using 1
  funext k
  simp only [mixture_entry, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

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

theorem basisExpectation_ensemble (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞)
    {v : J → E} (hv : Summable (fun j => ‖v j‖^2)) :
    basisExpectation b w (TraceEnsemble.operator v) = ∑' j, basisMoment b w (v j) := by
  have he (i : I) : ENNReal.ofReal (inner ℂ (b i) (TraceEnsemble.operator v (b i))).re =
      ∑' j, ENNReal.ofReal (‖inner ℂ (b i) (v j)‖^2) := by
    have hs := TraceEnsemble.hasSum_quadratic hv (b i)
    rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs.summable]
  simp only [basisExpectation, he, ← ENNReal.tsum_mul_left, basisMoment]
  exact ENNReal.tsum_comm

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

theorem diagonalVector_operator (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hs : Summable p) (T : E →L[ℂ] E)
    (he : ∀ j, T (b j) = (p j : ℂ) • b j) : operator (diagonalVector b p) = T := by
  have hb (j : J) : operator (diagonalVector b p) (b j) = T (b j) := by
    rw [diagonalVector_eigen b p hp hs j, he]
  ext x
  have hh := (operator (diagonalVector b p)).hasSum (b.hasSum_repr x)
  apply hh.unique
  convert T.hasSum (b.hasSum_repr x) using 1
  funext j
  simp only [ContinuousLinearMap.map_smul, hb]

end TraceEnsemble

namespace EntropyPhotonNumber
open QuantumTrace TraceEnsemble

end EntropyPhotonNumber

end

end OAI

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

end StochasticOverlap
end

section
open scoped BigOperators
variable {I J : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

theorem hasSum_entropy_eigenvalues (a : HilbertBasis I ℂ E) (b : HilbertBasis J ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive)
    (ht : HasSum (fun i => (inner ℂ (a i) (T (a i))).re) 1)
    (p : J → ℝ) (he : ∀ j, T (b j) = (p j : ℂ) • b j) {S : ℝ}
    (hS : HasSum (fun i => (inner ℂ (a i) (entropyOperator T (a i))).re) S) :
    HasSum (fun j => Real.negMulLog (p j)) S := by
  have hh := hasSum_trace_basis a b (entropyOperator_positive hp (norm_le_trace a hp ht)) hS
  have hev (j : J) : (inner ℂ (b j) (entropyOperator T (b j))).re = Real.negMulLog (p j) := by
    rw [entropyOperator_apply_eigenvector hp.isSymmetric (he j), inner_smul_right,
      inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
    simp
  simpa only [hev] using hh

end

variable {J : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

theorem entropy_hasSum {n : ℕ} (ρ : State n) (hρ : FiniteEnergy ρ) :
    HasSum (fun k => (inner ℂ (numberBasis n k) (entropyOperator ρ.op (numberBasis n k))).re)
      (entropy ρ) := by
  rw [entropy_eq_quantumTrace]
  have hh := (entropy_summable ρ hρ)
  simpa only [entropyOperator_eq_complex ρ.positive.isSymmetric, numberBasis_apply, entry]
    using hh.hasSum

theorem entropy_le_crossEntropy {n : ℕ} (ρ σ : State n) (hσ : FiniteEnergy σ)
    {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (hc : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re)) :
    entropy σ ≤ crossEntropy b p σ ∧
      (entropy σ = crossEntropy b p σ → σ = ρ) := by
  obtain ⟨I, a, q, hq, hqt, hqe⟩ := exists_positive_eigenbasis (numberBasis n)
    σ.positive (trace_one_numberBasis σ)
  have hS := hasSum_entropy_eigenvalues (numberBasis n) a σ.positive
    (trace_one_numberBasis σ) q hqe (entropy_hasSum σ hσ)
  have hC : HasSum (fun j => (inner ℂ (b j) (σ.op (b j))).re*(-Real.log (p j)))
      (crossEntropy b p σ) := by
    simpa only [crossEntropy, mul_comm] using hc.hasSum
  obtain ⟨hle, heq⟩ := quantum_klein a b ρ.positive.isSymmetric hq hqt hp hs hqe he hS hC
  exact ⟨hle, fun h => state_ext (heq h)⟩

theorem crossEntropy_self {n : ℕ} (ρ : State n) (hρ : FiniteEnergy ρ)
    {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) :
    crossEntropy b p ρ = entropy ρ := by
  have h := hasSum_entropy_eigenvalues (numberBasis n) b ρ.positive
    (trace_one_numberBasis ρ) p he (entropy_hasSum ρ hρ)
  rw [crossEntropy, ← h.tsum_eq]
  congr 1
  funext j
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  simp [Real.negMulLog]
  ring

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

theorem crossEntropy_mixture {n : ℕ} {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (t : ℝ) (ht : t ∈ Set.Icc 0 1) (ρ σ : State n)
    (hρ : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (ρ.op (b j))).re))
    (hσ : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re)) :
    crossEntropy b p (mixture t ht ρ σ) = t*crossEntropy b p ρ+(1-t)*crossEntropy b p σ := by
  have hh := (hρ.hasSum.mul_left t).add (hσ.hasSum.mul_left (1-t))
  have hf (j : J) : (-Real.log (p j))*(inner ℂ (b j) ((mixture t ht ρ σ).op (b j))).re =
      t*((-Real.log (p j))*(inner ℂ (b j) (ρ.op (b j))).re)+
      (1-t)*((-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re) := by
    simp only [mixture, add_apply, smul_apply, inner_add_right, inner_smul_right,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  unfold crossEntropy
  simpa only [hf] using hh.tsum_eq

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

theorem powerMoment_eq {n : ℕ} (m : ℕ) (ρ : State n) :
    powerMoment m ρ = ∑' k, ENNReal.ofReal ((1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re) := by
  unfold powerMoment matrixMoment
  congr 1
  funext k
  rw [ENNReal.ofReal_mul (pow_nonneg (by positivity) _),
    ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  rfl

theorem finiteMoment_iff {n : ℕ} (m : ℕ) (ρ : State n) :
    FiniteMoment m ρ ↔ powerMoment m ρ < ⊤ := by
  rw [powerMoment_eq]
  have hp (k : NumberIndex n) : 0 ≤ (1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re :=
    mul_nonneg (pow_nonneg (by positivity) _) (ρ.positive.re_inner_nonneg_right _)
  constructor
  · intro h
    exact h.tsum_ofReal_lt_top
  · intro h
    have hs := ENNReal.summable_toReal h.ne
    change Summable (fun k => (1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re)
    simpa only [ENNReal.toReal_ofReal (hp _)] using hs

end EntropyPhotonNumber

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Contraction ----
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
end

section
open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end

open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end BKM

namespace CenteredTests
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

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

omit [CompleteSpace E] in
theorem block_tail (M : Matrix I I ℂ) (j : J) : block b M (b (Sum.inr j)) = 0 := by
  classical
  simp [block, InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal]

variable [DecidableEq I]

end

open NormedSpace Matrix
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem trace_exp (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    (Matrix.trace (exp M)).re = ∑ i, Real.exp (hM.eigenvalues i) := by
  rw [exp_spectral M hM, Matrix.trace_mul_comm]
  rw [← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re]

end FiniteBlock

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I J : Type*}

variable [CompleteSpace E]

theorem basisExpectation_diagonal (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞)
    (c : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : Summable p) :
    basisExpectation b w (TraceEnsemble.operator (TraceEnsemble.diagonalVector c p)) =
      ∑' j, ENNReal.ofReal (p j)*basisMoment b w (c j) := by
  rw [basisExpectation_ensemble b w (by simpa only [TraceEnsemble.diagonalVector_norm_sq c p hp] using hs)]
  congr 1
  funext j
  rw [TraceEnsemble.diagonalVector, basisMoment_smul_coeff]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hp _)]

theorem eigenvector_moment_finite (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞)
    (c : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀ j, 0 < p j) (hs : Summable p)
    (hm : basisExpectation b w (TraceEnsemble.operator (TraceEnsemble.diagonalVector c p)) < ⊤)
    (j : J) : basisMoment b w (c j) < ⊤ := by
  rw [basisExpectation_diagonal b w c p (fun j => (hp j).le) hs] at hm
  have hj := (ENNReal.le_tsum j).trans_lt hm
  by_contra hn
  have he : basisMoment b w (c j) = ⊤ := top_le_iff.mp (not_lt.mp hn)
  rw [he] at hj
  simp [ENNReal.ofReal_pos.mpr (hp j) |>.ne'] at hj

end QuantumTrace

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

theorem expectation_eq_of_operator_eq (b : HilbertBasis J ℂ E)
    {K : Type*} {v : I → E} {w : K → E}
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (h : operator v = operator w) (Z : E →L[ℂ] E) : expectation v Z = expectation w Z := by
  have hh := hasSum_expectation_basis b hv Z
  rw [h] at hh
  exact hh.unique (hasSum_expectation_basis b hw Z)

end TraceEnsemble

namespace EntropyPhotonNumber

section
open TraceEnsemble

theorem expectation_ensemble {n : ℕ} (ρ : State n) {I : Type*} (v : I → Fock n)
    (hv : Summable (fun i => ‖v i‖^2)) (he : TraceEnsemble.operator v = ρ.op)
    (Z : Fock n →L[ℂ] Fock n) : expectation ρ Z = TraceEnsemble.expectation v Z := by
  exact TraceEnsemble.expectation_eq_of_operator_eq (channelNumberBasis n) (rootColumn_norm ρ).summable hv
    ((rootColumn_operator ρ).trans he.symm) Z

theorem hasSum_expectation_basis {n : ℕ} {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (ρ : State n) (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun j => inner ℂ (b j) (Z (ρ.op (b j)))) (expectation ρ Z) := by
  simpa only [rootColumn_operator, expectation] using
    TraceEnsemble.hasSum_expectation_basis b (rootColumn_norm ρ).summable Z

theorem expectation_add {n : ℕ} (ρ : State n) (X Y : Fock n →L[ℂ] Fock n) :
    expectation ρ (X+Y) = expectation ρ X+expectation ρ Y := by
  exact (hasSum_expectation_basis (channelNumberBasis n) ρ (X+Y)).unique (by
    simpa only [add_apply, inner_add_right] using
      (hasSum_expectation_basis (channelNumberBasis n) ρ X).add (hasSum_expectation_basis (channelNumberBasis n) ρ Y))

theorem expectation_smul {n : ℕ} (ρ : State n) (a : ℂ) (Z : Fock n →L[ℂ] Fock n) :
    expectation ρ (a • Z) = a*expectation ρ Z := by
  exact (hasSum_expectation_basis (channelNumberBasis n) ρ (a • Z)).unique (by
    simpa only [smul_apply, inner_smul_right] using
      (hasSum_expectation_basis (channelNumberBasis n) ρ Z).mul_left a)

end

open QuantumTrace TraceEnsemble

end EntropyPhotonNumber

namespace FiniteBlock

section
open QuantumTrace
variable {I J E K : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [DecidableEq I] in
 theorem basis_domain (a : HilbertBasis K ℂ E) (w : K → ℝ≥0∞)
    (b : HilbertBasis (I ⊕ J) ℂ E) (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1)
    (hm : basisExpectation a w (TraceEnsemble.operator (TraceEnsemble.diagonalVector b p)) < ⊤)
    (c : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (j : I ⊕ J) :
    basisMoment a w (basis b c j) < ⊤ := by
  have hv (j : I ⊕ J) : b j ∈ momentDomain a w :=
    eigenvector_moment_finite a w b p hp hs.summable hm j
  change basis b c j ∈ momentDomain a w
  cases j with
  | inr j => simpa only [basis_inr] using hv (Sum.inr j)
  | inl i =>
    rw [basis_inl, embed_apply]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hv (Sum.inl j)))

 theorem tilted_moment_finite (a : HilbertBasis K ℂ E) (w : K → ℝ≥0∞)
    (b : HilbertBasis (I ⊕ J) ℂ E) (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1)
    (hm : basisExpectation a w (TraceEnsemble.operator (TraceEnsemble.diagonalVector b p)) < ⊤)
    (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    basisExpectation a w (TraceEnsemble.operator
      (TraceEnsemble.diagonalVector (basis b hM.eigenvectorBasis) (weights p M hM))) < ⊤ := by
  rw [basisExpectation_diagonal a w _ _ (fun j => (weights_pos p hp hs M hM j).le)
    (weights_hasSum p hp hs M hM).summable]
  let P := (ENNReal.ofReal (partition p M hM))⁻¹
  have hP : P < ⊤ := by
    exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (partition_pos p hp hs M hM))
  have htail : (∑' j, ENNReal.ofReal (p (Sum.inr j))*basisMoment a w (b (Sum.inr j))) < ⊤ := by
    rw [basisExpectation_diagonal a w b p (fun j => (hp j).le) hs.summable] at hm
    exact (ENNReal.tsum_comp_le_tsum_of_injective Sum.inr_injective _).trans_lt hm
  have hh : HasSum (fun j : I ⊕ J => ENNReal.ofReal (weights p M hM j)*
      basisMoment a w (basis b hM.eigenvectorBasis j))
      ((∑ i, ENNReal.ofReal (weights p M hM (Sum.inl i))*
          basisMoment a w (basis b hM.eigenvectorBasis (Sum.inl i)))+
        ∑' j, ENNReal.ofReal (weights p M hM (Sum.inr j))*
          basisMoment a w (basis b hM.eigenvectorBasis (Sum.inr j))) :=
    HasSum.sum (hasSum_fintype _) ENNReal.summable.hasSum
  rw [hh.tsum_eq]
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (basis_domain a w b p hp hs hm hM.eigenvectorBasis (Sum.inl i)))
  · have he (j : J) : ENNReal.ofReal (weights p M hM (Sum.inr j))*
        basisMoment a w (basis b hM.eigenvectorBasis (Sum.inr j)) =
        P*(ENNReal.ofReal (p (Sum.inr j))*basisMoment a w (b (Sum.inr j))) := by
      rw [basis_inr]
      change ENNReal.ofReal (p (Sum.inr j)/partition p M hM)*_ = _
      rw [ENNReal.ofReal_div_of_pos (partition_pos p hp hs M hM), div_eq_mul_inv]
      dsimp only [P]
      ac_rfl
    simp only [he, ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top hP htail

end

variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [DecidableEq I] in
 theorem block_adjoint (b : HilbertBasis (I ⊕ J) ℂ E) (M : Matrix I I ℂ) :
    (block b M).adjoint = block b M.conjTranspose := by
  classical
  simp only [block, map_sum, map_smulₛₗ, InnerProductSpace.adjoint_rankOne]
  rw [Finset.sum_comm]
  rfl

omit [DecidableEq I] in
 theorem block_symmetric (b : HilbertBasis (I ⊕ J) ℂ E) (M : Matrix I I ℂ)
    (hM : M.IsHermitian) : (block b M).IsSymmetric := by
  rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, isSelfAdjoint_iff]
  change (block b M).adjoint = block b M
  rw [block_adjoint, hM.eq]

omit [DecidableEq I] [CompleteSpace E] in
 theorem block_add (b : HilbertBasis (I ⊕ J) ℂ E) (M N : Matrix I I ℂ) :
    block b (M+N) = block b M+block b N := by
  simp [block, add_smul, Finset.sum_add_distrib]

omit [DecidableEq I] [CompleteSpace E] in
 theorem block_smul (b : HilbertBasis (I ⊕ J) ℂ E) (t : ℂ) (M : Matrix I I ℂ) :
    block b (t • M) = t • block b M := by
  simp [block, Finset.smul_sum, smul_smul]

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

omit [CompleteSpace E] in
 theorem inner_block (b : HilbertBasis (I ⊕ J) ℂ E) (M : Matrix I I ℂ) (x : E) (i : I) :
    inner ℂ (b (Sum.inl i)) (block b M x) = ∑ j, M i j*inner ℂ (b (Sum.inl j)) x := by
  classical
  simp [block, InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal]

omit [CompleteSpace E] [DecidableEq I] in
 theorem inner_tail_block (b : HilbertBasis (I ⊕ J) ℂ E) (M : Matrix I I ℂ) (x : E) (j : J) :
    inner ℂ (b (Sum.inr j)) (block b M x) = 0 := by
  simp [block, InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal]

 omit [CompleteSpace E] [DecidableEq I] in
 theorem block_sub (b : HilbertBasis (I ⊕ J) ℂ E) (M N : Matrix I I ℂ) :
    block b (M-N) = block b M-block b N := by
  simp [block, sub_smul, Finset.sum_sub_distrib]

end FiniteBlock

namespace EntropyPhotonNumber

section
open QuantumTrace TraceEnsemble
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

 theorem expectation_block_matrix (σ : State n) (b : HilbertBasis (I ⊕ J) ℂ (Fock n))
    (M : Matrix I I ℂ) :
    expectation σ (FiniteBlock.block b M) =
      ∑ i, ∑ j, M i j*inner ℂ (b (Sum.inl j)) (σ.op (b (Sum.inl i))) := by
  have he (j : I ⊕ J) : inner ℂ (b j) (FiniteBlock.block b M (σ.op (b j))) =
      Sum.elim (fun i => ∑ k, M i k*inner ℂ (b (Sum.inl k)) (σ.op (b (Sum.inl i))))
        (fun _ => 0) j := by
    cases j with
    | inl i => exact FiniteBlock.inner_block b M _ i
    | inr j => exact FiniteBlock.inner_tail_block b M _ j
  have hh := hasSum_expectation_basis b σ (FiniteBlock.block b M)
  simp only [he] at hh
  have ht : HasSum (Sum.elim
      (fun i => ∑ k, M i k*inner ℂ (b (Sum.inl k)) (σ.op (b (Sum.inl i)))) (fun _ : J => (0:ℂ)))
      ((∑ i, ∑ k, M i k*inner ℂ (b (Sum.inl k)) (σ.op (b (Sum.inl i))))+0) :=
    HasSum.sum (hasSum_fintype _) hasSum_zero
  simpa only [add_zero] using hh.unique ht

end

section
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

theorem block_relativeEntropy_lower (σ : State n) (hσ : FiniteEnergy σ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (hc : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re))
    (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    (expectation σ (FiniteBlock.block b M)).re-
      (expectation σ (FiniteBlock.block b (Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ))))).re-
      Real.log (FiniteBlock.partition p M hM) ≤ relativeEntropy b p σ := by
  have ht := block_crossEntropy σ b p hp hs hc M hM
  have hK := (entropy_le_crossEntropy (blockState b p hp hs M hM) σ hσ _ _
    (FiniteBlock.weights_pos p hp hs M hM) (FiniteBlock.weights_hasSum p hp hs M hM)
    (spectralState_eigen _ _ _ _) ht.summable).1
  change entropy σ ≤ ∑' j, _ at hK
  rw [ht.tsum_eq] at hK
  dsimp only [relativeEntropy]
  linarith

end

open QuantumTrace TraceEnsemble
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

 theorem blockState_finiteMoment (ρ : State n) {m : ℕ} (hm : FiniteMoment m ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    FiniteMoment m (blockState b p hp hs M hM) := by
  rw [finiteMoment_iff] at hm ⊢
  have ht := FiniteBlock.tilted_moment_finite (numberBasis n)
    (fun k => (1+(totalNumber k : ℝ≥0∞))^m) b p hp hs ?_ M hM
  · simpa only [powerMoment, TensorLp.matrixMoment, basisExpectation,
      numberBasis_apply, numberKet, blockState, spectralState] using ht
  · rw [diagonalVector_operator b p (fun j => (hp j).le) hs.summable ρ.op he]
    simpa only [powerMoment, TensorLp.matrixMoment, basisExpectation,
      numberBasis_apply, numberKet] using hm

omit [Fintype I] [DecidableEq I] in
 theorem crossEntropy_self_summable (ρ : State n) (hρ : FiniteEnergy ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) :
    Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (ρ.op (b j))).re) := by
  have h := hasSum_entropy_eigenvalues (numberBasis n) b ρ.positive
    (trace_one_numberBasis ρ) p he (entropy_hasSum ρ hρ)
  convert h.summable using 1
  funext j
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  simp [Real.negMulLog]
  ring

 theorem blockState_crossEntropy_finite (ρ : State n) (hρ : FiniteEnergy ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    Summable (fun j => (-Real.log (p j))*
      (inner ℂ (b j) ((blockState b p hp hs M hM).op (b j))).re) := by
  have hc := (crossEntropy_self_summable ρ hρ b p he).comp_injective Sum.inr_injective
  apply Summable.sum _ (hasSum_fintype _).summable
  apply (hc.div_const (FiniteBlock.partition p M hM)).congr
  intro j
  dsimp only [Function.comp_def]
  rw [blockState_operator ρ b p hp hs he M hM]
  simp only [smul_apply, sub_apply, add_apply, FiniteBlock.block_tail, add_zero, sub_zero,
    inner_smul_right, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

 theorem blockState_relativeEntropy (ρ : State n) (hρ : FiniteEnergy ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian)
    (hσ : FiniteEnergy (blockState b p hp hs M hM)) :
    relativeEntropy b p (blockState b p hp hs M hM) =
      (expectation (blockState b p hp hs M hM) (FiniteBlock.block b M)).re-
      (expectation (blockState b p hp hs M hM)
        (FiniteBlock.block b (Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ))))).re-
      Real.log (FiniteBlock.partition p M hM) := by
  have hc := block_crossEntropy (blockState b p hp hs M hM) b p hp hs
    (blockState_crossEntropy_finite ρ hρ b p hp hs he M hM) M hM
  have hh := crossEntropy_self (blockState b p hp hs M hM) hσ
    (FiniteBlock.basis b hM.eigenvectorBasis) (FiniteBlock.weights p M hM)
    (spectralState_eigen _ _ _ _)
  change (∑' j, _) = _ at hh
  rw [hc.tsum_eq] at hh
  dsimp only [relativeEntropy]
  linarith

 theorem blockState_block_entry (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian)
    (i j : I) :
    inner ℂ (b (Sum.inl i)) ((blockState b p hp hs M hM).op (b (Sum.inl j))) =
      exp M i j/(FiniteBlock.partition p M hM : ℂ) := by
  rw [blockState_operator ρ b p hp hs he M hM]
  simp only [smul_apply, sub_apply, add_apply, inner_smul_right, inner_sub_right, inner_add_right,
    he, inner_smul_right, FiniteBlock.inner_block]
  simp [orthonormal_iff_ite.mp b.orthonormal, Matrix.diagonal_apply,
    mul_ite, div_eq_mul_inv, mul_comm]
  by_cases h : i = j <;> simp [h]

 theorem blockState_block_expectation (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian)
    (Z : Matrix I I ℂ) :
    expectation (blockState b p hp hs M hM) (FiniteBlock.block b Z) =
      Matrix.trace (Z*exp M)/(FiniteBlock.partition p M hM : ℂ) := by
  rw [expectation_block_matrix]
  simp only [blockState_block_entry ρ b p hp hs he M hM, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Finset.sum_div, mul_div_assoc]

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
theorem exp_sub_eq_integral (a b : A) :
    exp b - exp a = ∫ s in (0 : ℝ)..1, exp ((1-s) • a) * (b-a) * exp (s • b) := by
  have hd (s : ℝ) : HasDerivAt (fun t : ℝ => exp ((1-t) • a) * exp (t • b))
      (exp ((1-s) • a) * (b-a) * exp (s • b)) s := by
    have hleft : HasDerivAt (fun t : ℝ => exp ((1-t) • a))
        (-(exp ((1-s) • a) * a)) s := by
      simpa [Function.comp_def] using (hasDerivAt_exp_smul_const a (1-s)).scomp s
        ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s))
    have hright := hasDerivAt_exp_smul_const' b s
    have heq : exp ((1-s) • a) * (b-a) * exp (s • b) =
        -(exp ((1-s) • a) * a) * exp (s • b) +
          exp ((1-s) • a) * (b * exp (s • b)) := by noncomm_ring
    rw [heq]
    exact hleft.mul hright
  have hc : Continuous (fun s : ℝ => exp ((1-s) • a) * (b-a) * exp (s • b)) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 1)
  simpa using h.symm

theorem exp_add_smul_sub (a z : A) (t : ℝ) :
    exp (a+t • z) - exp a =
      t • (∫ s in (0 : ℝ)..1, exp ((1-s) • a) * z * exp (s • (a+t • z))) := by
  rw [exp_sub_eq_integral, ← intervalIntegral.integral_smul]
  congr 1
  funext s
  simp

theorem continuous_duhamel (a z : A) :
    Continuous (fun t : ℝ =>
      ∫ s in (0 : ℝ)..1, exp ((1-s) • a) * z * exp (s • (a+t • z))) := by
  have hc : Continuous (Function.uncurry (fun t s : ℝ =>
      exp ((1-s) • a) * z * exp (s • (a+t • z)))) := by fun_prop
  have hh := continuous_parametric_integral_of_continuous (μ := volume) hc (s := Set.Icc (0:ℝ) 1) isCompact_Icc
  convert! hh using 1
  funext t
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

theorem hasDerivAt_exp_add_smul_zero (a z : A) :
    HasDerivAt (fun t : ℝ => exp (a+t • z))
      (∫ s in (0 : ℝ)..1, exp ((1-s) • a) * z * exp (s • a)) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hc := (continuous_duhamel a z).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)
  apply Filter.Tendsto.congr' ?_ (by simpa only [zero_smul, add_zero] using hc)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  rw [slope_def_module]
  simp only [zero_smul, add_zero, sub_zero, exp_add_smul_sub, smul_smul, inv_mul_cancel₀ ht0,
    one_smul]

theorem hasDerivAt_exp_add_smul (a z : A) (t : ℝ) :
    HasDerivAt (fun u : ℝ => exp (a+u • z))
      (∫ s in (0 : ℝ)..1, exp ((1-s) • (a+t • z)) * z * exp (s • (a+t • z))) t := by
  have hh := (hasDerivAt_exp_add_smul_zero (a+t • z) z).scomp_of_eq t
    ((hasDerivAt_id t).sub_const t) (by simp)
  convert! hh using 1
  · funext u
    simp [sub_smul]
  · simp

end

section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
attribute [local instance] OAI.QuantumCalculus.instNormedAlgebraRat_oAI_1
theorem trace_duhamel (τ : A →L[ℝ] ℝ) (hτ : ∀ x y, τ (x*y) = τ (y*x))
    (a z : A) :
    τ (∫ s in (0 : ℝ)..1, exp ((1-s) • a) * z * exp (s • a)) = τ (exp a * z) := by
  have hc : Continuous (fun s : ℝ => exp ((1-s) • a) * z * exp (s • a)) := by fun_prop
  rw [← τ.intervalIntegral_comp_comm (hc.intervalIntegrable 0 1)]
  have heq (s : ℝ) : τ (exp ((1-s) • a) * z * exp (s • a)) = τ (exp a * z) := by
    rw [hτ, ← mul_assoc, ← exp_add_of_commute
      (((Commute.refl a).smul_left s).smul_right (1-s)), ← add_smul]
    simp
  simp_rw [heq]
  simp

theorem hasDerivAt_trace_exp (τ : A →L[ℝ] ℝ) (hτ : ∀ x y, τ (x*y) = τ (y*x))
    (a z : A) (t : ℝ) :
    HasDerivAt (fun u : ℝ => τ (exp (a+u • z))) (τ (exp (a+t • z)*z)) t := by
  have hh := τ.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_add_smul a z t)
  simpa only [Function.comp_def, trace_duhamel τ hτ] using hh

theorem hasDerivAt_trace_exp_mul (τ : A →L[ℝ] ℝ)
    (a z : A) (t : ℝ) :
    HasDerivAt (fun u : ℝ => τ (exp (a+u • z)*z))
      (τ ((∫ s in (0 : ℝ)..1,
         exp ((1-s) • (a+t • z))*z*exp (s • (a+t • z)))*z)) t := by
  exact τ.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_exp_add_smul a z t).mul_const z)

end

section
open scoped Matrix.Norms.Operator ComplexConjugate
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem matrixReTrace_cyclic (M N : Matrix I I ℂ) :
    matrixReTrace (M*N) = matrixReTrace (N*M) := by
  simp only [matrixReTrace_apply, Matrix.trace_mul_comm M N]

theorem exp_real_diagonal (v : I → ℝ) (s : ℝ) :
    exp (s • Matrix.diagonal (fun i => (v i : ℂ))) =
      Matrix.diagonal (fun i => (Real.exp (s*v i) : ℂ)) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  simp [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

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

theorem finite_block_partition_expansion (p : I → ℝ) (hp : ∀ i, 0 < p i)
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) (c : ℝ)
    (hn : c + ∑ i, p i = 1) :
    (fun t : ℝ => Real.log (c + matrixReTrace
        (exp (Matrix.diagonal (fun i => (Real.log (p i) : ℂ)) + t • Z))) -
      (∑ i, p i*(Z i i).re)*t -
      ((∑ i, ∑ j, DiagonalForms.System.logMean (p i) (p j) * Complex.normSq (Z i j)) -
        (∑ i, p i*(Z i i).re)^2)/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
  let a := Matrix.diagonal (fun i => (Real.log (p i) : ℂ))
  have hea : exp a = Matrix.diagonal (fun i => (p i : ℂ)) := by
    simpa only [one_smul, one_mul, Real.exp_log (hp _)] using
      exp_real_diagonal (fun i => Real.log (p i)) 1
  have htr : matrixReTrace (exp a) = ∑ i, p i := by
    rw [hea, matrixReTrace_apply, Matrix.trace_diagonal]
    simp
  have hm : matrixReTrace (exp a*Z) = ∑ i, p i*(Z i i).re := by
    rw [hea, matrixReTrace_apply]
    simp [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  have hh := log_partition_expansion (matrixReTrace (I := I)) matrixReTrace_cyclic a Z c
    (by erw [htr]; exact hn)
  erw [hm, matrix_duhamel_hessian p hp Z hZ] at hh
  exact hh

end

section
open Filter Asymptotics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
attribute [local instance] OAI.QuantumCalculus.instNormedAlgebraRat_oAI_3
theorem relative_partition_expansion (τ : A →L[ℝ] ℝ)
    (hτ : ∀ x y, τ (x*y) = τ (y*x)) (a z : A) (c : ℝ)
    (hn : c+τ (exp a) = 1) :
    (fun t : ℝ => t*(τ (exp (a+t • z)*z)/(c+τ (exp (a+t • z))))-
      Real.log (c+τ (exp (a+t • z)))-
      (τ ((∫ s in (0:ℝ)..1, exp ((1-s) • a)*z*exp (s • a))*z)-
        (τ (exp a*z))^2)/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
  let P : ℝ → ℝ := fun t => c+τ (exp (a+t • z))
  let M : ℝ → ℝ := fun t => τ (exp (a+t • z)*z)
  let d : ℝ := τ ((∫ s in (0:ℝ)..1, exp ((1-s) • a)*z*exp (s • a))*z)-
    (τ (exp a*z))^2
  have hP (t : ℝ) : HasDerivAt P (M t) t := (hasDerivAt_trace_exp τ hτ a z t).const_add c
  have hP0 : P 0 = 1 := by simpa [P] using hn
  have hd := (hasDerivAt_trace_exp_mul τ a z 0).div (hP 0) (by simp [hP0])
  have hd' : HasDerivAt (fun t => M t/P t) d 0 := by
    convert hd using 1 <;>
    first | rfl |
      simp only [d, M, zero_smul, add_zero, hP0, mul_one, div_one, pow_two]
  have he : (fun t => M t/P t-M 0-d*t) =o[𝓝 (0:ℝ)] (fun t => t) := by
    simpa only [hP0, div_one, sub_zero, smul_eq_mul, mul_comm d] using hd'.isLittleO
  have he2 : (fun t => (M t/P t-M 0-d*t)*t) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
    simpa only [pow_two] using he.mul_isBigO (isBigO_refl (fun t : ℝ => t) (𝓝 0))
  have hq := log_partition_expansion τ hτ a z c hn
  have hh := he2.sub hq
  convert! hh using 1
  · funext t
    dsimp only [P, M, d]
    simp only [zero_smul, add_zero]
    ring

end

open Matrix Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

 theorem finite_block_relative_expansion (p : I → ℝ) (hp : ∀ i, 0 < p i)
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) (c : ℝ)
    (hn : c + ∑ i, p i = 1) :
    (fun t : ℝ => t*(matrixReTrace
        (exp (Matrix.diagonal (fun i => (Real.log (p i) : ℂ))+t • Z)*Z)/
        (c+matrixReTrace (exp (Matrix.diagonal (fun i => (Real.log (p i) : ℂ))+t • Z))))-
      Real.log (c+matrixReTrace (exp (Matrix.diagonal (fun i => (Real.log (p i) : ℂ))+t • Z)))-
      ((∑ i, ∑ j, DiagonalForms.System.logMean (p i) (p j) * Complex.normSq (Z i j)) -
        (∑ i, p i*(Z i i).re)^2)/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
  let a := Matrix.diagonal (fun i => (Real.log (p i) : ℂ))
  have hea : exp a = Matrix.diagonal (fun i => (p i : ℂ)) := by
    simpa only [one_smul, one_mul, Real.exp_log (hp _)] using
      exp_real_diagonal (fun i => Real.log (p i)) 1
  have htr : matrixReTrace (exp a) = ∑ i, p i := by
    rw [hea, matrixReTrace_apply, Matrix.trace_diagonal]
    simp
  have hm : matrixReTrace (exp a*Z) = ∑ i, p i*(Z i i).re := by
    rw [hea, matrixReTrace_apply]
    simp [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  have hh := relative_partition_expansion (matrixReTrace (I := I)) matrixReTrace_cyclic a Z c
    (by erw [htr]; exact hn)
  erw [hm, matrix_duhamel_hessian p hp Z hZ] at hh
  exact hh

end QuantumCalculus

namespace FiniteBlock
open QuantumCalculus
variable {I J : Type*} [Fintype I] [DecidableEq I]

 theorem partition_trace (p : I ⊕ J → ℝ) (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    partition p M hM = (∑' j, p (Sum.inr j))+matrixReTrace (exp M) := by
  rw [matrixReTrace_apply, trace_exp]
  rfl

omit [DecidableEq I] in
 theorem tail_normalization (p : I ⊕ J → ℝ) (hs : HasSum p 1) :
    (∑' j, p (Sum.inr j)) + ∑ i, p (Sum.inl i) = 1 := by
  have hh := HasSum.sum (f := p) (hasSum_fintype (fun i => p (Sum.inl i)))
    (hs.summable.comp_injective Sum.inr_injective).hasSum
  rw [add_comm]
  exact hh.unique hs

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumCalculus QuantumTrace Filter Asymptotics
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

 theorem blockTilt_relativeEntropy (ρ : State n) (hρ : FiniteEnergy ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) (t : ℝ)
    (ht : FiniteEnergy (blockTilt b p hp hs Z hZ t)) :
    relativeEntropy b p (blockTilt b p hp hs Z hZ t) =
      t*(matrixReTrace (exp (FiniteBlock.tiltMatrix p Z t)*Z)/
        ((∑' j, p (Sum.inr j))+matrixReTrace (exp (FiniteBlock.tiltMatrix p Z t))))-
      Real.log ((∑' j, p (Sum.inr j))+matrixReTrace (exp (FiniteBlock.tiltMatrix p Z t))) := by
  rw [blockTilt, blockState_relativeEntropy ρ hρ b p hp hs he _ _ ht]
  have hsZ : t • Z = (t : ℂ) • Z := by ext i j; simp
  rw [show FiniteBlock.block b (FiniteBlock.tiltMatrix p Z t) =
      FiniteBlock.block b (Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ)))+
      (t:ℂ) • FiniteBlock.block b Z by
        rw [FiniteBlock.tiltMatrix, FiniteBlock.block_add, hsZ, FiniteBlock.block_smul]]
  rw [expectation_add, expectation_smul]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [blockState_block_expectation ρ b p hp hs he _ _ Z]
  rw [Matrix.trace_mul_comm Z, Complex.div_ofReal_re,
    FiniteBlock.partition_trace]
  simp only [matrixReTrace_apply]
  ring

 theorem blockTilt_relativeEntropy_expansion (ρ : State n) (hρ : FiniteEnergy ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian)
    (ht : ∀ t, FiniteEnergy (blockTilt b p hp hs Z hZ t)) :
    (fun t : ℝ => relativeEntropy b p (blockTilt b p hp hs Z hZ t)-
      ((∑ i, ∑ j, DiagonalForms.System.logMean (p (Sum.inl i)) (p (Sum.inl j)) * Complex.normSq (Z i j)) -
        (∑ i, p (Sum.inl i)*(Z i i).re)^2)/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
  simp_rw [blockTilt_relativeEntropy ρ hρ b p hp hs he Z hZ _ (ht _), FiniteBlock.tiltMatrix]
  exact finite_block_relative_expansion _ (fun i => hp (Sum.inl i)) Z hZ _
    (FiniteBlock.tail_normalization p hs)

 theorem blockTilt_finiteMoment (ρ : State n) {m : ℕ} (hm : FiniteMoment m ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) (t : ℝ) :
    FiniteMoment m (blockTilt b p hp hs Z hZ t) :=
  blockState_finiteMoment ρ hm b p hp hs he _ _

 theorem blockTilt_relativeEntropy_expansion_of_moment (ρ : State n) (hm : FiniteMoment 4 ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) :
    (fun t : ℝ => relativeEntropy b p (blockTilt b p hp hs Z hZ t)-
      ((∑ i, ∑ j, DiagonalForms.System.logMean (p (Sum.inl i)) (p (Sum.inl j)) * Complex.normSq (Z i j)) -
        (∑ i, p (Sum.inl i)*(Z i i).re)^2)/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) :=
  blockTilt_relativeEntropy_expansion ρ (finiteMoment_finiteEnergy (by norm_num) hm)
    b p hp hs he Z hZ (fun t => finiteMoment_finiteEnergy (by norm_num)
      (blockTilt_finiteMoment ρ hm b p hp hs he Z hZ t))

 theorem block_relativeEntropy_tilt_lower (σ : State n) (hσ : FiniteEnergy σ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (hc : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re))
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) (t : ℝ) :
    t*(expectation σ (FiniteBlock.block b Z)).re-
      Real.log ((∑' j, p (Sum.inr j))+matrixReTrace (exp (FiniteBlock.tiltMatrix p Z t))) ≤
      relativeEntropy b p σ := by
  have hh := block_relativeEntropy_lower σ hσ b p hp hs hc
    (FiniteBlock.tiltMatrix p Z t) (FiniteBlock.tiltMatrix_hermitian p Z hZ t)
  have hsZ : t • Z = (t : ℂ) • Z := by ext i j; simp
  rw [show FiniteBlock.block b (FiniteBlock.tiltMatrix p Z t) =
      FiniteBlock.block b (Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ)))+
      (t:ℂ) • FiniteBlock.block b Z by
        rw [FiniteBlock.tiltMatrix, FiniteBlock.block_add, hsZ, FiniteBlock.block_smul],
    expectation_add, expectation_smul] at hh
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hh
  rw [FiniteBlock.partition_trace] at hh
  linarith

end EntropyPhotonNumber

namespace FiniteBlock
variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
 theorem block_basis (b : HilbertBasis (I ⊕ J) ℂ E) (M : Matrix I I ℂ) (j : I) :
    block b M (b (Sum.inl j)) = ∑ i, M i j • b (Sum.inl i) := by
  simp [block, InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal]

omit [CompleteSpace E] [DecidableEq I] in
 theorem trace_block_bounded (b : HilbertBasis (I ⊕ J) ℂ E) (A : Matrix I I ℂ)
    (Z : E →L[ℂ] E) :
    HasSum (fun j => inner ℂ (b j) (Z (block b A (b j))))
      (Matrix.trace (A * entries b Z)) := by
  classical
  have he (j : I ⊕ J) : inner ℂ (b j) (Z (block b A (b j))) =
      Sum.elim (fun j => ∑ i, A i j*inner ℂ (b (Sum.inl j)) (Z (b (Sum.inl i)))) (fun _ => 0) j := by
    cases j with
    | inl j => simp [block_basis]
    | inr j => simp only [block_tail, map_zero, inner_zero_right, Sum.elim_inr]
  simp_rw [he]
  have h := HasSum.sum (f := Sum.elim (fun j => ∑ i, A i j*inner ℂ (b (Sum.inl j)) (Z (b (Sum.inl i)))) (fun _ : J => (0:ℂ)))
    (hasSum_fintype _) (hasSum_zero : HasSum (fun _ : J => (0:ℂ)) 0)
  have heq : (∑ j, ∑ i, A i j * inner ℂ (b (Sum.inl j)) (Z (b (Sum.inl i)))) =
      Matrix.trace (A * entries b Z) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, entries]
    exact Finset.sum_comm
  simpa only [Function.comp_def, Sum.elim_inl, add_zero, heq] using h

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

 theorem blockState_expectation (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian)
    (Z : Fock n →L[ℂ] Fock n) :
    expectation (blockState b p hp hs M hM) Z =
      (expectation ρ Z + Matrix.trace ((exp M-Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ)))*
        FiniteBlock.entries b Z))/(FiniteBlock.partition p M hM : ℂ) := by
  have hρ := hasSum_expectation_basis b ρ Z
  have hA := FiniteBlock.trace_block_bounded b
    (exp M-Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ))) Z
  have hσ := hasSum_expectation_basis b (blockState b p hp hs M hM) Z
  rw [blockState_operator ρ b p hp hs he M hM] at hσ
  simp only [smul_apply, sub_apply, add_apply, map_smul, map_sub, map_add,
    inner_smul_right, inner_sub_right, inner_add_right] at hσ
  have hh := (hρ.add hA).mul_left ((FiniteBlock.partition p M hM : ℂ)⁻¹)
  simp only [FiniteBlock.block_sub, sub_apply, map_sub, inner_sub_right] at hh
  apply hσ.unique
  rw [div_eq_mul_inv, mul_comm]
  convert! hh using 1
  funext j
  ring

end EntropyPhotonNumber

namespace QuantumCalculus
open Matrix Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

 theorem matrix_duhamel_mixed_integrand (v : I → ℝ) (X Y : Matrix I I ℂ) (s : ℝ) :
    matrixReTrace (exp ((1-s) • Matrix.diagonal (fun i => (v i : ℂ)))*X*
      exp (s • Matrix.diagonal (fun i => (v i : ℂ)))*Y) =
      ∑ i, ∑ j, Real.exp ((1-s)*v i+s*v j)*(X i j*Y j i).re := by
  rw [exp_real_diagonal, exp_real_diagonal, matrixReTrace_apply]
  have he : (Matrix.diagonal (fun i => (Real.exp ((1-s)*v i) : ℂ))*X*
      Matrix.diagonal (fun i => (Real.exp (s*v i) : ℂ))*Y).trace =
      ∑ i, ∑ j, (Real.exp ((1-s)*v i) : ℂ)*X i j*(Real.exp (s*v j) : ℂ)*Y j i := by
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [he]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.exp_add]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

 theorem matrix_duhamel_mixed (p : I → ℝ) (hp : ∀ i, 0 < p i) (X Y : Matrix I I ℂ) :
    matrixReTrace ((∫ s in (0:ℝ)..1,
      exp ((1-s) • Matrix.diagonal (fun i => (Real.log (p i) : ℂ)))*X*
      exp (s • Matrix.diagonal (fun i => (Real.log (p i) : ℂ))))*Y) =
      ∑ i, ∑ j, DiagonalForms.System.logMean (p i) (p j)*(X i j*Y j i).re := by
  let a : Matrix I I ℂ := Matrix.diagonal (fun i => (Real.log (p i) : ℂ))
  have hc : Continuous (fun s : ℝ => exp ((1-s) • a)*X*exp (s • a)) := by fun_prop
  have hm := ((ContinuousLinearMap.mul ℝ (Matrix I I ℂ)).flip Y).intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := volume) 0 1)
  change (∫ s in (0:ℝ)..1, (exp ((1-s) • a)*X*exp (s • a))*Y) =
    (∫ s in (0:ℝ)..1, exp ((1-s) • a)*X*exp (s • a))*Y at hm
  change matrixReTrace ((∫ s in (0:ℝ)..1, exp ((1-s) • a)*X*exp (s • a))*Y) = _
  rw [← hm]
  have hcy : Continuous (fun s : ℝ => exp ((1-s) • a)*X*exp (s • a)*Y) := hc.mul continuous_const
  trans ∫ s in (0:ℝ)..1, matrixReTrace (exp ((1-s) • a)*X*exp (s • a)*Y)
  · exact (matrixReTrace.intervalIntegral_comp_comm (hcy.intervalIntegrable (μ := volume) 0 1)).symm
  simp_rw [a, matrix_duhamel_mixed_integrand]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_mul_const, integral_exp_affine_log (hp i) (hp j)]
    · intro j _
      exact (by fun_prop : Continuous (fun s : ℝ =>
        Real.exp ((1-s)*Real.log (p i)+s*Real.log (p j))*(X i j*Y j i).re)).intervalIntegrable 0 1
  · intro i _
    apply Continuous.intervalIntegrable
    fun_prop

 theorem normalized_expectation_deriv (p : I → ℝ) (hp : ∀ i, 0 < p i)
    (X Y : Matrix I I ℂ) (c μ : ℝ) (hn : c+∑ i, p i = 1) :
    HasDerivAt (fun t : ℝ =>
      (μ+matrixReTrace ((exp (Matrix.diagonal (fun i => (Real.log (p i) : ℂ))+t • X)-
        Matrix.diagonal (fun i => (p i : ℂ)))*Y))/
      (c+matrixReTrace (exp (Matrix.diagonal (fun i => (Real.log (p i) : ℂ))+t • X))))
      ((∑ i, ∑ j, DiagonalForms.System.logMean (p i) (p j)*(X i j*Y j i).re)-
        μ*(∑ i, p i*(X i i).re)) 0 := by
  let a : Matrix I I ℂ := Matrix.diagonal (fun i => (Real.log (p i) : ℂ))
  have hea : exp a = Matrix.diagonal (fun i => (p i : ℂ)) := by
    simpa only [one_smul, one_mul, Real.exp_log (hp _)] using
      exp_real_diagonal (fun i => Real.log (p i)) 1
  have htr : matrixReTrace (exp a) = ∑ i, p i := by
    rw [hea, matrixReTrace_apply, Matrix.trace_diagonal]
    simp
  have hm : matrixReTrace (exp a*X) = ∑ i, p i*(X i i).re := by
    rw [hea, matrixReTrace_apply]
    simp [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  have hd := (hasDerivAt_trace_exp matrixReTrace matrixReTrace_cyclic a X 0).const_add c
  have hv := matrixReTrace.hasFDerivAt.comp_hasDerivAt 0
    (((hasDerivAt_exp_add_smul a X 0).sub_const (Matrix.diagonal (fun i => (p i : ℂ)))).mul_const Y)
  simp only [zero_smul, add_zero] at hd hv
  have hnorm : c+matrixReTrace (exp a) = 1 := htr ▸ hn
  have hbase : exp a-Matrix.diagonal (fun i => (p i : ℂ)) = 0 := by rw [hea, sub_self]
  have hh := (hv.const_add μ).div hd (by
    change c+matrixReTrace (exp (a+(0:ℝ) • X)) ≠ 0
    rw [zero_smul, add_zero, hnorm]
    exact one_ne_zero)
  simp only [Function.comp_def, zero_smul, add_zero] at hh
  erw [hbase, zero_mul, map_zero, hnorm, hm, matrix_duhamel_mixed p hp X Y] at hh
  simp only [add_zero, mul_one, one_pow, div_one] at hh
  convert! hh using 1

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

theorem quadratic_coefficient_nonneg {f : ℝ → ℝ} {a : ℝ}
    (he : (fun t => f t-a*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2))
    (hf : ∀ᶠ t in 𝓝 (0:ℝ), 0 ≤ f t) : 0 ≤ a := by
  by_contra h
  have ha : 0 < -a/2 := by linarith
  have hh := he.bound ha
  obtain ⟨δ,hδ,heδ⟩ := Metric.eventually_nhds_iff.mp (hh.and hf)
  have ht : dist (δ/2) (0:ℝ) < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
  obtain ⟨h1,h2⟩ := heδ ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (δ/2))] at h1
  have hp : 0 < (δ/2)^2 := sq_pos_of_pos (by positivity)
  have h3 := (le_abs_self (f (δ/2)-a*(δ/2)^2)).trans h1
  nlinarith

theorem hessian_comparison {D P E : ℝ → ℝ} {α Qi Qo m d : ℝ}
    (hD : (fun t => D t-Qi/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2))
    (hP : (fun t => P t-m*t-Qo/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2))
    (hE : HasDerivAt E d 0) (hE0 : E 0 = m)
    (hle : ∀ᶠ t in 𝓝 (0:ℝ), t*E t-P t ≤ α*D t) :
    2*d ≤ α*Qi+Qo := by
  have hE' : (fun t => E t-m-d*t) =o[𝓝 (0:ℝ)] (fun t => t) := by
    simpa only [hE0, sub_zero, smul_eq_mul, mul_comm d] using hE.isLittleO
  have hE2 : (fun t => t*(E t-m-d*t)) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
    simpa only [pow_two] using (isBigO_refl (fun t : ℝ => t) (𝓝 0)).mul_isLittleO hE'
  have hh := ((hD.const_mul_left α).add hP).sub hE2
  have hh' : (fun t => (α*D t-(t*E t-P t))-(α*Qi/2+Qo/2-d)*t^2)
      =o[𝓝 (0:ℝ)] (fun t => t^2) := by
    convert! hh using 1
    funext t
    ring
  have hn := quadratic_coefficient_nonneg hh' (hle.mono (fun _ h => sub_nonneg.mpr h))
  linarith
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

 theorem KrausFlow.dual_entry (F : KrausFlow n) (Z : Fock n →L[ℂ] Fock n) (x y : Fock n) :
    HasSum (fun i => inner ℂ (F.V i x) (Z (F.V i y))) (inner ℂ x (F.dual Z y)) :=
  KrausBounded.dual_entry F.V F.norm Z x y

 theorem KrausFlow.expectation_dual (F : KrausFlow n) (ρ : State n)
    (Z : Fock n →L[ℂ] Fock n) : expectation (F.map ρ) Z = expectation ρ (F.dual Z) := by
  have hn := TraceEnsemble.kraus_hasSum F.norm (rootColumn_norm ρ)
  have he := F.ensemble (NumberIndex n) (rootColumn ρ) ρ (rootColumn_norm ρ) (rootColumn_operator ρ)
  rw [expectation_ensemble (F.map ρ) _ hn.summable he]
  have hs := (TraceEnsemble.summable_expectation_norm hn.summable Z).of_norm
  change (∑' z : F.I × NumberIndex n, inner ℂ (F.V z.1 (rootColumn ρ z.2))
    (Z (F.V z.1 (rootColumn ρ z.2)))) = _
  have hc (j : NumberIndex n) := F.dual_entry Z (rootColumn ρ j) (rootColumn ρ j)
  have hh := ((Equiv.prodComm (NumberIndex n) F.I).hasSum_iff.2 hs.hasSum).prod_fiberwise hc
  exact hh.tsum_eq.symm

 theorem KrausFlow.dual_selfAdjoint (F : KrausFlow n) {Z : Fock n →L[ℂ] Fock n}
    (hZ : IsSelfAdjoint Z) : IsSelfAdjoint (F.dual Z) :=
  KrausBounded.dual_selfAdjoint F.V F.norm hZ

 theorem expectation_mixture (α : ℝ) (hα : α ∈ Set.Icc 0 1) (ρ σ : State n)
    (Z : Fock n →L[ℂ] Fock n) :
    expectation (mixture α hα ρ σ) Z = (α : ℂ)*expectation ρ Z+(1-α : ℂ)*expectation σ Z := by
  have hh := ((hasSum_expectation_basis (numberBasis n) ρ Z).mul_left (α : ℂ)).add
    ((hasSum_expectation_basis (numberBasis n) σ Z).mul_left (1-α : ℂ))
  apply (hasSum_expectation_basis (numberBasis n) (mixture α hα ρ σ) Z).unique
  simpa only [mixture, smul_apply, add_apply, map_add, map_smul, inner_add_right, inner_smul_right, Complex.ofReal_sub, Complex.ofReal_one] using hh

end

section
open QuantumCalculus QuantumTrace Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

 theorem blockTilt_expectation_formula (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (X : Matrix I I ℂ) (hX : X.IsHermitian) (Z : Fock n →L[ℂ] Fock n) (t : ℝ) :
    (expectation (blockTilt b p hp hs X hX t) Z).re =
      ((expectation ρ Z).re+matrixReTrace
        ((exp (FiniteBlock.tiltMatrix p X t)-Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ)))*
          FiniteBlock.entries b Z))/
      ((∑' j, p (Sum.inr j))+matrixReTrace (exp (FiniteBlock.tiltMatrix p X t))) := by
  rw [blockTilt, blockState_expectation ρ b p hp hs he,
    Complex.div_ofReal_re, Complex.add_re, FiniteBlock.partition_trace]
  rfl

 theorem blockTilt_expectation_deriv (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (X : Matrix I I ℂ) (hX : X.IsHermitian) (Z : Fock n →L[ℂ] Fock n) :
    HasDerivAt (fun t : ℝ => (expectation (blockTilt b p hp hs X hX t) Z).re)
      ((∑ i, ∑ j, DiagonalForms.System.logMean (p (Sum.inl i)) (p (Sum.inl j))*
        (X i j*inner ℂ (b (Sum.inl j)) (Z (b (Sum.inl i)))).re)-
          (expectation ρ Z).re*(∑ i, p (Sum.inl i)*(X i i).re)) 0 := by
  simp_rw [blockTilt_expectation_formula ρ b p hp hs he X hX Z]
  exact normalized_expectation_deriv (fun i => p (Sum.inl i)) (fun i => hp (Sum.inl i))
    X (FiniteBlock.entries b Z) _ _ (FiniteBlock.tail_normalization p hs)

 theorem blockTilt_expectation_zero (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (X : Matrix I I ℂ) (hX : X.IsHermitian) (Z : Fock n →L[ℂ] Fock n) :
    (expectation (blockTilt b p hp hs X hX 0) Z).re = (expectation ρ Z).re := by
  rw [blockTilt_expectation_formula ρ b p hp hs he X hX Z]
  have h0 : exp (FiniteBlock.tiltMatrix p X 0) = Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ)) := by
    simpa only [FiniteBlock.tiltMatrix, zero_smul, add_zero, one_smul, one_mul,
      Real.exp_log (hp _)] using exp_real_diagonal (fun i => Real.log (p (Sum.inl i))) 1
  rw [h0, sub_self, zero_mul, map_zero, add_zero, matrixReTrace_apply, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re]
  rw [FiniteBlock.tail_normalization p hs, div_one]

 theorem expectation_block_of_eigen (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (Z : Matrix I I ℂ) :
    expectation ρ (FiniteBlock.block b Z) = ∑ i, (p (Sum.inl i) : ℂ)*Z i i := by
  have heq (j : I ⊕ J) : inner ℂ (b j) (FiniteBlock.block b Z (ρ.op (b j))) =
      Sum.elim (fun i => (p (Sum.inl i) : ℂ)*Z i i) (fun _ => 0) j := by
    rw [he, map_smul, inner_smul_right]
    cases j with
    | inl i => simp [FiniteBlock.block_basis, inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
    | inr j => simp [FiniteBlock.block_tail]
  have hh := HasSum.sum (f := Sum.elim (fun i => (p (Sum.inl i) : ℂ)*Z i i) (fun _ : J => (0:ℂ)))
    (hasSum_fintype _) (hasSum_zero : HasSum (fun _ : J => (0:ℂ)) 0)
  exact (hasSum_expectation_basis b ρ (FiniteBlock.block b Z)).unique (by
    simpa only [heq, Function.comp_def, Sum.elim_inl, add_zero] using hh)

 theorem expectation_block_of_eigen_re (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (Z : Matrix I I ℂ) :
    (expectation ρ (FiniteBlock.block b Z)).re = ∑ i, p (Sum.inl i)*(Z i i).re := by
  rw [expectation_block_of_eigen ρ b p he]
  simp

end

open QuantumCalculus QuantumTrace Filter Asymptotics

 theorem crossEntropy_mixture_summable {n : ℕ} {J : Type*}
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (ρ σ : State n)
    (hρ : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (ρ.op (b j))).re))
    (hσ : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re)) :
    Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) ((mixture t ht ρ σ).op (b j))).re) := by
  apply ((hρ.mul_left t).add (hσ.mul_left (1-t))).congr
  intro j
  simp only [mixture, add_apply, smul_apply, inner_add_right, inner_smul_right,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

 theorem one_port_relative_entropy_bound {n : ℕ} {J L : Type*}
    (F : KrausFlow n) (τ : State n) (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1)
    (c a β ζ C : ℝ) (hc : 0 < c) (ha : 0 < a)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (d : HilbertBasis L ℂ (Fock n)) (q : L → ℝ)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hτ : FiniteEnergy τ)
    (hcross : ∀ σ, FiniteMoment 4 σ →
      Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) ((F.map σ).op (d j))).re))
    (hcτ : Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) (τ.op (d j))).re))
    (hlog : ∀ σ, FiniteMoment 4 σ → crossEntropy b p σ =
      (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d q (F.map σ)+(β/a)*energy σ+C)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-
        a*entropy ρ+β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-
        a*entropy σ+β*energy σ+ζ*numberMoment 4 σ)
    (σ : State n) (hmσ : FiniteMoment 4 σ) :
    relativeEntropy d q (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ) ≤
      (a/c)*relativeEntropy b p σ := by
  let ht : 1-κ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  have hself := crossEntropy_self ρ (finiteMoment_finiteEnergy (by norm_num) hmρ) b p he
  have hself0 := crossEntropy_self (mixture (1-κ) ht (F.map ρ) τ)
    (mixture_finiteEnergy _ _ (F.finiteEnergy _ (finiteMoment_finiteEnergy (by norm_num) hmρ)) hτ) d q he0
  rw [crossEntropy_mixture d q (1-κ) ht (F.map ρ) τ (hcross ρ hmρ) hcτ] at hself0
  rw [hlog ρ hmρ] at hself
  have hself' := congrArg (fun x => a*x) hself
  have hcancel (x : ℝ) : a*(x/a) = x := mul_div_cancel₀ x ha.ne'
  simp only [mul_add, ← mul_assoc, hcancel] at hself'
  have hσ := hmin σ hmσ
  have hid : a*relativeEntropy b p σ-c*relativeEntropy d q (mixture (1-κ) ht (F.map σ) τ) =
      (c*entropy (mixture (1-κ) ht (F.map σ) τ)-a*entropy σ+β*energy σ+ζ*numberMoment 4 σ)-
      (c*entropy (mixture (1-κ) ht (F.map ρ) τ)-a*entropy ρ+β*energy ρ+ζ*numberMoment 4 ρ) := by
    unfold relativeEntropy
    rw [hlog σ hmσ, crossEntropy_mixture d q (1-κ) ht (F.map σ) τ (hcross σ hmσ) hcτ]
    field_simp [ha.ne']
    linear_combination hself'-c*hself0
  have hb : 0 ≤ a*relativeEntropy b p σ-c*relativeEntropy d q (mixture (1-κ) ht (F.map σ) τ) := by
    rw [hid]
    exact sub_nonneg.mpr hσ
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hc).mpr (by nlinarith)

end EntropyPhotonNumber

namespace FiniteBlock
open DiagonalForms.System
variable {I J : Type*} [Fintype I]
end FiniteBlock

namespace EntropyPhotonNumber
open QuantumCalculus QuantumTrace Filter Asymptotics
open scoped Matrix.Norms.Operator

 theorem flow_finite_hessian {n : ℕ} {I J K L : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (F : KrausFlow n) (τ : State n) (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1)
    (c a β ζ C : ℝ) (hc : 0 < c) (ha : 0 < a)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (d : HilbertBasis (K ⊕ L) ℂ (Fock n)) (q : K ⊕ L → ℝ)
    (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hτ : FiniteEnergy τ)
    (hcross : ∀ σ, FiniteMoment 4 σ →
      Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) ((F.map σ).op (d j))).re))
    (hcτ : Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) (τ.op (d j))).re))
    (hlog : ∀ σ, FiniteMoment 4 σ → crossEntropy b p σ =
      (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d q (F.map σ)+(β/a)*energy σ+C)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-
        a*entropy ρ+β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-
        a*entropy σ+β*energy σ+ζ*numberMoment 4 σ)
    (X : Matrix I I ℂ) (hX : X.IsHermitian) (Z : Matrix K K ℂ) (hZ : Z.IsHermitian) :
    2*((1-κ)*FiniteBlock.covariance p X (FiniteBlock.entries b (F.dual (FiniteBlock.block d Z)))
      (expectation ρ (F.dual (FiniteBlock.block d Z))).re) ≤
      (a/c)*FiniteBlock.variance p X+FiniteBlock.variance q Z := by
  let hκ' : 1-κ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  let σ := fun t => blockTilt b p hp hs X hX t
  let ω := fun t => mixture (1-κ) hκ' (F.map (σ t)) τ
  let Y := FiniteBlock.block d Z
  have hm (t : ℝ) : FiniteMoment 4 (σ t) := blockTilt_finiteMoment ρ hmρ b p hp hs he X hX t
  have hf (t : ℝ) : FiniteEnergy (ω t) := mixture_finiteEnergy _ _
    (F.finiteEnergy _ (finiteMoment_finiteEnergy (by norm_num) (hm t))) hτ
  have hcro (t : ℝ) : Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) ((ω t).op (d j))).re) :=
    crossEntropy_mixture_summable d q (1-κ) hκ' (F.map (σ t)) τ (hcross _ (hm t)) hcτ
  have hD := blockTilt_relativeEntropy_expansion_of_moment ρ hmρ b p hp hs he X hX
  have hP := finite_block_partition_expansion (fun i => q (Sum.inl i)) (fun i => hq (Sum.inl i)) Z hZ
    (∑' j, q (Sum.inr j)) (FiniteBlock.tail_normalization q ht)
  have hd := blockTilt_expectation_deriv ρ b p hp hs he X hX (F.dual Y)
  have hE : HasDerivAt (fun t => (expectation (ω t) Y).re)
      ((1-κ)*FiniteBlock.covariance p X (FiniteBlock.entries b (F.dual Y)) (expectation ρ (F.dual Y)).re) 0 := by
    convert! (hd.const_mul (1-κ)).add_const (κ*(expectation τ Y).re) using 1
    funext t
    dsimp only [ω]
    rw [expectation_mixture, F.expectation_dual]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_mul, sub_self, sub_zero]
    ring
  have hE0 : (expectation (ω 0) Y).re = FiniteBlock.mean q Z := by
    trans (expectation (mixture (1-κ) hκ' (F.map ρ) τ) Y).re
    · dsimp only [ω]
      rw [expectation_mixture, expectation_mixture, F.expectation_dual, F.expectation_dual]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_mul, sub_self, sub_zero]
      rw [show (expectation (σ 0) (F.dual Y)).re = (expectation ρ (F.dual Y)).re from
        blockTilt_expectation_zero ρ b p hp hs he X hX (F.dual Y)]
    · exact expectation_block_of_eigen_re _ d q he0 Z
  have hi (t : ℝ) : t*(expectation (ω t) Y).re-
      Real.log ((∑' j, q (Sum.inr j))+matrixReTrace (exp (FiniteBlock.tiltMatrix q Z t))) ≤
      (a/c)*relativeEntropy b p (σ t) := by
    have hlo := block_relativeEntropy_tilt_lower (ω t) (hf t) d q hq ht (hcro t) Z hZ t
    exact hlo.trans (one_port_relative_entropy_bound F τ κ hκ c a β ζ C hc ha ρ hmρ b p d q
      he he0 hτ hcross hcτ hlog hmin (σ t) (hm t))
  exact hessian_comparison hD hP hE hE0 (Filter.Eventually.of_forall hi)

end EntropyPhotonNumber

namespace FiniteBlock
open DiagonalForms.System
open scoped ComplexConjugate
variable {I J : Type*} [Fintype I]

 theorem mean_scale (p : I ⊕ J → ℝ) (X : Matrix I I ℂ) (t : ℝ) :
    mean p ((t:ℂ) • X) = t*mean p X := by
  simp only [mean, Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; ring

 theorem variance_scale (p : I ⊕ J → ℝ) (X : Matrix I I ℂ) (t : ℝ) :
    variance p ((t:ℂ) • X) = t^2*variance p X := by
  rw [variance, mean_scale, variance]
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
  have hh : (∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j)) *
      (t^2*Complex.normSq (X i j))) =
      t^2*(∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j)) := by
    simp_rw [Finset.mul_sum]
    congr 1; ext i; congr 1; ext j; ring
  simp only [← pow_two]
  rw [hh]
  ring

 theorem covariance_scale_self (p : I ⊕ J → ℝ) (X : Matrix I I ℂ) (hX : X.IsHermitian)
    (μ t : ℝ) : covariance p ((t:ℂ) • X) X μ =
      t*((∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j))-μ*mean p X) := by
  have hc (i j : I) : (X j i) = conj (X i j) := by
    exact (congrFun (congrFun hX.eq j) i).symm
  rw [covariance, mean_scale]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hh (i j : I) : ((t:ℂ)*X i j*X j i).re = t*Complex.normSq (X i j) := by
    rw [hc i j, mul_assoc, Complex.mul_conj]
    simp
  simp_rw [hh]
  have he : (∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j)) *
      (t*Complex.normSq (X i j))) =
      t*(∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j)) := by
    simp_rw [Finset.mul_sum]
    congr 1; ext i; congr 1; ext j; ring
  rw [he]
  ring
end FiniteBlock

namespace BKM
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem compression_mean (b : HilbertBasis J ℂ E) (p : J → ℝ) (Y : E →L[ℂ] E) (s : Finset J) :
    FiniteBlock.mean (p ∘ Equiv.sumCompl (fun j => j ∈ s))
      (FiniteBlock.entries (reindexBasis b (Equiv.sumCompl (fun j => j ∈ s))) Y) =
      ∑ j ∈ s, p j*(entry b Y j j).re := by
  classical
  simp only [FiniteBlock.mean, FiniteBlock.entries, reindexBasis_apply, Function.comp_apply,
    Equiv.sumCompl_apply_inl, entry]
  exact (Finset.sum_subtype s (fun _ => Iff.rfl) (fun j => p j*(inner ℂ (b j) (Y (b j))).re)).symm

 theorem compression_quadratic (b : HilbertBasis J ℂ E) (p : J → ℝ) (Y : E →L[ℂ] E) (s : Finset J) :
    (∑ i : s, ∑ j : s, logMean (p i.val) (p j.val)*Complex.normSq
      (FiniteBlock.entries (reindexBasis b (Equiv.sumCompl (fun j => j ∈ s))) Y i j)) =
      ∑ i ∈ s, ∑ j ∈ s, logMean (p i) (p j)*Complex.normSq (entry b Y i j) := by
  classical
  simp only [FiniteBlock.entries, reindexBasis_apply, Equiv.sumCompl_apply_inl, entry,
    Finset.sum_subtype s (fun _ => Iff.rfl)]

 theorem compression_hessian_to_variance (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : Summable p) (Y : E →L[ℂ] E) (μ α γ W : ℝ)
    (hm : HasSum (fun j => p j*(entry b Y j j).re) μ) (hα : 0 < α)
    (hY : IsSelfAdjoint Y)
    (h : ∀ (s : Finset J) (t : ℝ),
      let b' := reindexBasis b (Equiv.sumCompl (fun j => j ∈ s))
      let p' := p ∘ Equiv.sumCompl (fun j => j ∈ s)
      let X := FiniteBlock.entries b' Y
      2*(γ*FiniteBlock.covariance p' ((t:ℂ) • X) X μ) ≤
        α*FiniteBlock.variance p' ((t:ℂ) • X)+W) :
    γ^2*((∑' ij : J × J, logMean (p ij.1) (p ij.2)*Complex.normSq (entry b Y ij.1 ij.2))-μ^2) ≤ α*W := by
  classical
  apply finite_hessian_to_variance _ _ μ _ α γ W (logMean_summable b p hp hs Y).hasSum hm hα
  intro s t
  have hh := h s t
  dsimp only at hh
  have hX : (FiniteBlock.entries (reindexBasis b (Equiv.sumCompl (fun j => j ∈ s))) Y).IsHermitian := by
    ext i j
    change conj (inner ℂ (reindexBasis b _ (Sum.inl j)) (Y (reindexBasis b _ (Sum.inl i)))) =
      inner ℂ (reindexBasis b _ (Sum.inl i)) (Y (reindexBasis b _ (Sum.inl j)))
    rw [inner_conj_symm]
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hY) _ _
  rw [FiniteBlock.covariance_scale_self _ _ hX, FiniteBlock.variance_scale,
    FiniteBlock.variance, compression_mean] at hh
  simp only [Function.comp_apply, Equiv.sumCompl_apply_inl, compression_quadratic] at hh
  nlinarith
end BKM

namespace EntropyPhotonNumber

section
open QuantumTrace DiagonalForms.System
open scoped ComplexConjugate
variable {n : ℕ} {J K L : Type*} [Fintype K] [DecidableEq K]

 theorem crossEntropy_reindex {M : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (e : M ≃ J) (ρ : State n) : crossEntropy (BKM.reindexBasis b e) (p ∘ e) ρ = crossEntropy b p ρ := by
  simp only [crossEntropy, BKM.reindexBasis_apply, Function.comp_def]
  exact e.tsum_eq (fun j : J => (-Real.log (p j))*(inner ℂ (b j) (ρ.op (b j))).re)

 theorem finite_entries_selfAdjoint {I T E : Type*} [Fintype I] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (b : HilbertBasis (I ⊕ T) ℂ E)
    (Z : E →L[ℂ] E) (hZ : IsSelfAdjoint Z) : (FiniteBlock.entries b Z).IsHermitian := by
  ext i j
  change conj (inner ℂ (b (Sum.inl j)) (Z (b (Sum.inl i)))) = inner ℂ (b (Sum.inl i)) (Z (b (Sum.inl j)))
  rw [inner_conj_symm]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hZ) _ _

 theorem expectation_eigen_hasSum (ρ : State n) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun j => p j*(BKM.entry b Z j j).re) (expectation ρ Z).re := by
  have h := (hasSum_expectation_basis b ρ Z).mapL Complex.reCLM
  simpa only [he, map_smul, inner_smul_right, Complex.reCLM_apply, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, BKM.entry] using h

 theorem flow_full_hessian (F : KrausFlow n) (τ : State n) (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1)
    (c a β ζ C : ℝ) (hc : 0 < c) (ha : 0 < a) (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (d : HilbertBasis (K ⊕ L) ℂ (Fock n)) (q : K ⊕ L → ℝ)
    (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hτ : FiniteEnergy τ)
    (hcross : ∀ σ, FiniteMoment 4 σ →
      Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) ((F.map σ).op (d j))).re))
    (hcτ : Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) (τ.op (d j))).re))
    (hlog : ∀ σ, FiniteMoment 4 σ → crossEntropy b p σ =
      (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d q (F.map σ)+(β/a)*energy σ+C)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-
        a*entropy ρ+β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-
        a*entropy σ+β*energy σ+ζ*numberMoment 4 σ)
    (Z : Matrix K K ℂ) (hZ : Z.IsHermitian) :
    (1-κ)^2*((∑' ij : J × J, logMean (p ij.1) (p ij.2)*
      Complex.normSq (BKM.entry b (F.dual (FiniteBlock.block d Z)) ij.1 ij.2))-
        (expectation ρ (F.dual (FiniteBlock.block d Z))).re^2) ≤ (a/c)*FiniteBlock.variance q Z := by
  classical
  let Y := F.dual (FiniteBlock.block d Z)
  let μ := (expectation ρ Y).re
  have hY : IsSelfAdjoint Y := F.dual_selfAdjoint (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (FiniteBlock.block_symmetric d Z hZ))
  apply BKM.compression_hessian_to_variance b p hp hs.summable Y μ (a/c) (1-κ)
    (FiniteBlock.variance q Z) (expectation_eigen_hasSum ρ b p he Y) (div_pos ha hc) hY
  intro s t
  let e := Equiv.sumCompl (fun j => j ∈ s)
  let b' := BKM.reindexBasis b e
  let p' := p ∘ e
  let X := FiniteBlock.entries b' Y
  have hX := finite_entries_selfAdjoint b' Y hY
  have hl' (σ : State n) (hh : FiniteMoment 4 σ) : crossEntropy b' p' σ =
      (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d q (F.map σ)+(β/a)*energy σ+C := by
    rw [crossEntropy_reindex]
    exact hlog σ hh
  have he' (j) : ρ.op (b' j) = (p' j : ℂ) • b' j := by
    simpa only [b', p', BKM.reindexBasis_apply, Function.comp_apply] using he (e j)
  have htself : IsSelfAdjoint (t : ℂ) := by
    change conj (t : ℂ) = (t : ℂ)
    exact Complex.conj_ofReal t
  have hh := flow_finite_hessian F τ κ hκ c a β ζ C hc ha ρ hmρ b' p'
    (fun j => hp (e j)) (e.hasSum_iff.mpr hs) d q hq ht he' he0 hτ hcross hcτ hl'
    hmin ((t:ℂ) • X) (hX.smul htself) Z hZ
  exact hh

end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {K L : Type*} [Fintype K] [DecidableEq K]

end EntropyPhotonNumber

namespace BKM
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem entry_real_smul (b : HilbertBasis J ℂ E) (c : ℝ) (Z : E →L[ℂ] E) (i j : J) :
    entry b (c • Z) i j=(c:ℂ)*entry b Z i j := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), entry_smul]
  rfl

variable [CompleteSpace E]

theorem entry_realPart (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (i j : J) :
    entry b (realPart Z : E →L[ℂ] E) i j=(entry b Z i j+conj (entry b Z j i))/2 := by
  rw [realPart_apply_coe, entry_real_smul, entry_add, ContinuousLinearMap.star_eq_adjoint, entry_adjoint]
  push_cast
  ring

theorem entry_imaginaryPart (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (i j : J) :
    entry b (imaginaryPart Z : E →L[ℂ] E) i j=-Complex.I*(entry b Z i j-conj (entry b Z j i))/2 := by
  rw [imaginaryPart_apply_coe, entry_smul, entry_real_smul, entry_sub,
    ContinuousLinearMap.star_eq_adjoint, entry_adjoint]
  push_cast
  ring

end BKM

namespace Complex
open scoped _root_.Complex
open scoped ComplexConjugate
 theorem normSq_polar_parts (z w : ℂ) :
    _root_.Complex.normSq ((z+conj w)/2)+_root_.Complex.normSq (-_root_.Complex.I*(z-conj w)/2)=(_root_.Complex.normSq z+_root_.Complex.normSq w)/2 := by
  simp only [div_eq_mul_inv, _root_.Complex.normSq_apply, _root_.Complex.add_re, _root_.Complex.add_im, _root_.Complex.mul_re, _root_.Complex.mul_im, _root_.Complex.sub_re, _root_.Complex.sub_im,
    _root_.Complex.conj_re, _root_.Complex.conj_im, _root_.Complex.neg_re, _root_.Complex.neg_im, _root_.Complex.I_re, _root_.Complex.I_im, _root_.Complex.inv_re, _root_.Complex.inv_im]
  norm_num
  ring
end Complex

namespace BKM

section
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem quadratic_adjoint (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) :
    quadratic b p Z.adjoint=quadratic b p Z := by
  simp only [quadratic, entry_adjoint, Complex.normSq_conj]
  have h := (Equiv.prodComm J J).tsum_eq (fun ij : J × J => logMean (p ij.1) (p ij.2)*Complex.normSq (entry b Z ij.1 ij.2))
  convert! h using 1
  congr 1
  ext ij
  exact congrArg (fun x => x*Complex.normSq (entry b Z ij.2 ij.1)) (logMean_symm _ _)

theorem quadratic_parts (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀ j,0 < p j) (hs : Summable p)
    (Z : E →L[ℂ] E) :
    quadratic b p (realPart Z : E →L[ℂ] E)+quadratic b p (imaginaryPart Z : E →L[ℂ] E)=quadratic b p Z := by
  have hr := logMean_summable b p hp hs (realPart Z : E →L[ℂ] E)
  have hi := logMean_summable b p hp hs (imaginaryPart Z : E →L[ℂ] E)
  have hz := logMean_summable b p hp hs Z
  have ha := logMean_summable b p hp hs Z.adjoint
  have he (ij : J × J) :
      logMean (p ij.1) (p ij.2)*Complex.normSq (entry b (realPart Z : E →L[ℂ] E) ij.1 ij.2)+
      logMean (p ij.1) (p ij.2)*Complex.normSq (entry b (imaginaryPart Z : E →L[ℂ] E) ij.1 ij.2)=
      (logMean (p ij.1) (p ij.2)*Complex.normSq (entry b Z ij.1 ij.2)+
      logMean (p ij.1) (p ij.2)*Complex.normSq (entry b Z.adjoint ij.1 ij.2))/2 := by
    rw [← mul_add, entry_realPart, entry_imaginaryPart, Complex.normSq_polar_parts, entry_adjoint, Complex.normSq_conj]
    ring
  have hh := hr.hasSum.add hi.hasSum
  simp_rw [he] at hh
  have ht := (hz.hasSum.add ha.hasSum).div_const 2
  have heq := hh.unique ht
  change quadratic b p (realPart Z : E →L[ℂ] E)+quadratic b p (imaginaryPart Z : E →L[ℂ] E)=
    (quadratic b p Z+quadratic b p Z.adjoint)/2 at heq
  rw [quadratic_adjoint] at heq
  linarith

end

section
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem mean_adjoint (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) :
    mean b p Z.adjoint=conj (mean b p Z) := by
  simp only [mean, entry_adjoint, Complex.conj_tsum, map_mul, Complex.conj_ofReal]

theorem mean_parts (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    (Z : E →L[ℂ] E) :
    mean b p (realPart Z : E →L[ℂ] E)=(mean b p Z).re ∧
    mean b p (imaginaryPart Z : E →L[ℂ] E)=(mean b p Z).im := by
  have hr (j : J) :
      (p j : ℂ)*entry b (realPart Z : E →L[ℂ] E) j j =
        (p j : ℂ)*(entry b Z j j + conj (entry b Z j j))/2 := by rw [entry_realPart]; ring
  have hi (j : J) :
      (p j : ℂ)*entry b (imaginaryPart Z : E →L[ℂ] E) j j =
        -Complex.I*((p j : ℂ)*entry b Z j j-conj ((p j : ℂ)*entry b Z j j))/2 := by
    rw [entry_imaginaryPart]
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have h := mean_summable b p hp hs Z
  have hc := (h.hasSum.mapL Complex.conjCLE.toContinuousLinearMap)
  change HasSum (fun j => conj ((p j : ℂ)*entry b Z j j)) (conj (mean b p Z)) at hc
  constructor
  · have hh := (h.hasSum.add hc).div_const 2
    have he (j : J) :
        ((p j : ℂ)*entry b Z j j+conj ((p j : ℂ)*entry b Z j j))/2=
          (p j : ℂ)*entry b (realPart Z : E →L[ℂ] E) j j := by
      rw [hr, map_mul, Complex.conj_ofReal]; ring
    simp_rw [he] at hh
    rw [mean, hh.tsum_eq]
    change (mean b p Z+conj (mean b p Z))/2=((mean b p Z).re:ℂ)
    rw [Complex.add_conj]
    push_cast
    ring
  · have hh := ((h.hasSum.sub hc).mul_left (-Complex.I)).div_const 2
    simp_rw [← hi] at hh
    rw [mean, hh.tsum_eq]
    change -Complex.I*(mean b p Z-conj (mean b p Z))/2=((mean b p Z).im:ℂ)
    rw [Complex.sub_conj]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring

theorem variance_parts (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (Z : E →L[ℂ] E) :
    variance b p (realPart Z : E →L[ℂ] E)+variance b p (imaginaryPart Z : E →L[ℂ] E)=variance b p Z := by
  obtain ⟨hr,hi⟩ := mean_parts b p (fun j => (hp j).le) hs Z
  simp only [variance, hr, hi, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have h := quadratic_parts b p hp hs Z
  linarith

end

open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem entry_block (b : HilbertBasis (I ⊕ J) ℂ E) (X : Matrix I I ℂ) (i j : I ⊕ J) :
    entry b (FiniteBlock.block b X) i j=match i,j with
      | Sum.inl a,Sum.inl c => X a c
      | _,_ => 0 := by
  classical
  cases i <;> cases j <;>
    simp [entry, FiniteBlock.block_basis, FiniteBlock.block_tail,
      orthonormal_iff_ite.mp b.orthonormal]

omit [CompleteSpace E] in
theorem mean_block (b : HilbertBasis (I ⊕ J) ℂ E) (p : I ⊕ J → ℝ) (X : Matrix I I ℂ) :
    mean b p (FiniteBlock.block b X)=∑ i, (p (Sum.inl i):ℂ)*X i i := by
  have hh := HasSum.sum (f := fun j : I ⊕ J => (p j:ℂ)*entry b (FiniteBlock.block b X) j j)
    (by simpa only [Function.comp_def, entry_block] using hasSum_fintype (fun i : I => (p (Sum.inl i):ℂ)*X i i))
    (by simpa only [Function.comp_def, entry_block, mul_zero] using (hasSum_zero : HasSum (fun _ : J => (0:ℂ)) 0))
  simpa only [add_zero, mean] using hh.tsum_eq

theorem quadratic_block (b : HilbertBasis (I ⊕ J) ℂ E) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (X : Matrix I I ℂ) :
    quadratic b p (FiniteBlock.block b X)=
      ∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j) := by
  rw [quadratic, (logMean_summable b p hp hs (FiniteBlock.block b X)).tsum_prod]
  have row (i : I) :
      (∑' j : I ⊕ J, logMean (p (Sum.inl i)) (p j)*Complex.normSq (entry b (FiniteBlock.block b X) (Sum.inl i) j))=
      ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j) := by
    have hh := HasSum.sum (f := fun j : I ⊕ J => logMean (p (Sum.inl i)) (p j)*Complex.normSq (entry b (FiniteBlock.block b X) (Sum.inl i) j))
      (by simpa only [Function.comp_def, entry_block] using hasSum_fintype (fun j : I => logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j)))
      (by simpa only [Function.comp_def, entry_block, Complex.normSq_zero, mul_zero] using (hasSum_zero : HasSum (fun _ : J => (0:ℝ)) 0))
    simpa only [add_zero] using hh.tsum_eq
  have hh := HasSum.sum (f := fun i : I ⊕ J => ∑' j : I ⊕ J, logMean (p i) (p j)*Complex.normSq (entry b (FiniteBlock.block b X) i j))
    (by simpa only [Function.comp_def, row] using hasSum_fintype (fun i : I => ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j)))
    (by simpa only [Function.comp_def, entry_block, Complex.normSq_zero, mul_zero, tsum_zero] using (hasSum_zero : HasSum (fun _ : J => (0:ℝ)) 0))
  simpa only [add_zero] using hh.tsum_eq

omit [Fintype I] [DecidableEq I] in
theorem normSq_mean_selfAdjoint (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (Z : E →L[ℂ] E) (hZ : IsSelfAdjoint Z) : Complex.normSq (mean b p Z)=(mean b p Z).re^2 := by
  have hh := mean_adjoint b p Z
  rw [show Z.adjoint=Z from hZ] at hh
  have hi := congrArg Complex.im hh
  simp only [Complex.conj_im] at hi
  rw [Complex.normSq_apply]
  nlinarith

theorem variance_block (b : HilbertBasis (I ⊕ J) ℂ E) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (X : Matrix I I ℂ) (hX : X.IsHermitian) :
    variance b p (FiniteBlock.block b X)=FiniteBlock.variance p X := by
  rw [variance, quadratic_block b p hp hs, normSq_mean_selfAdjoint b p _
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (FiniteBlock.block_symmetric b X hX)), mean_block]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, FiniteBlock.variance, FiniteBlock.mean]

omit [DecidableEq I] in
 theorem block_realPart (b : HilbertBasis (I ⊕ J) ℂ E) (X : Matrix I I ℂ) :
    FiniteBlock.block b (realPart X : Matrix I I ℂ)=(realPart (FiniteBlock.block b X) : E →L[ℂ] E) := by
  simp only [realPart_apply_coe, RCLike.real_smul_eq_coe_smul (K := ℂ),
    FiniteBlock.block_smul, FiniteBlock.block_add, ContinuousLinearMap.star_eq_adjoint,
    Matrix.star_eq_conjTranspose, FiniteBlock.block_adjoint]

omit [DecidableEq I] in
 theorem block_imaginaryPart (b : HilbertBasis (I ⊕ J) ℂ E) (X : Matrix I I ℂ) :
    FiniteBlock.block b (imaginaryPart X : Matrix I I ℂ)=(imaginaryPart (FiniteBlock.block b X) : E →L[ℂ] E) := by
  simp only [imaginaryPart_apply_coe, RCLike.real_smul_eq_coe_smul (K := ℂ),
    FiniteBlock.block_smul, FiniteBlock.block_sub, ContinuousLinearMap.star_eq_adjoint,
    Matrix.star_eq_conjTranspose, FiniteBlock.block_adjoint]
end BKM

namespace EntropyPhotonNumber

section
open scoped ComplexConjugate ComplexStarModule
variable {n : ℕ} {J : Type*}

theorem mean_expectation (ρ : State n) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (he : ∀j, ρ.op (b j)=(p j:ℂ) • b j) (Z : Fock n →L[ℂ] Fock n) :
    BKM.mean b p Z=expectation ρ Z := by
  have hh := hasSum_expectation_basis b ρ Z
  simp only [he, map_smul, inner_smul_right] at hh
  exact hh.tsum_eq

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
 theorem KrausFlow.dual_adjoint (F : KrausFlow n) (Z : Fock n →L[ℂ] Fock n) :
    F.dual Z.adjoint=(F.dual Z).adjoint := KrausBounded.dual_adjoint F.V F.norm Z
 theorem KrausFlow.dual_realPart (F : KrausFlow n) (Z : Fock n →L[ℂ] Fock n) :
    F.dual (realPart Z : Fock n →L[ℂ] Fock n)=(realPart (F.dual Z) : Fock n →L[ℂ] Fock n) := by
  simp only [realPart_apply_coe, ← Complex.coe_smul,
    ContinuousLinearMap.star_eq_adjoint, F.dual_smul, F.dual_add, F.dual_adjoint]

 theorem KrausFlow.dual_imaginaryPart (F : KrausFlow n) (Z : Fock n →L[ℂ] Fock n) :
    F.dual (imaginaryPart Z : Fock n →L[ℂ] Fock n)=(imaginaryPart (F.dual Z) : Fock n →L[ℂ] Fock n) := by
  simp only [imaginaryPart_apply_coe, ← Complex.coe_smul,
    ContinuousLinearMap.star_eq_adjoint, F.dual_smul, F.dual_sub, F.dual_adjoint]

end

section
open QuantumTrace DiagonalForms.System
open scoped ComplexStarModule
variable {n : ℕ} {K L J : Type*} [Fintype K] [DecidableEq K]

theorem complex_component_hessian (F : KrausFlow n) (c a κ : ℝ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (d : HilbertBasis (K ⊕ L) ℂ (Fock n)) (q : K ⊕ L → ℝ)
    (hq : ∀j,0 < q j) (ht : Summable q)
    (h : ∀ (Z : Matrix K K ℂ), Z.IsHermitian →
      (1-κ)^2*BKM.variance b p (F.dual (FiniteBlock.block d Z)) ≤ (a/c)*FiniteBlock.variance q Z)
    (Z : Matrix K K ℂ) :
    (1-κ)^2*BKM.variance b p (F.dual (FiniteBlock.block d Z)) ≤
      (a/c)*BKM.variance d q (FiniteBlock.block d Z) := by
  have hr : (realPart Z : Matrix K K ℂ).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr selfAdjoint.isSelfAdjoint
  have hi : (imaginaryPart Z : Matrix K K ℂ).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr selfAdjoint.isSelfAdjoint
  have h1 := h (realPart Z) hr
  have h2 := h (imaginaryPart Z) hi
  rw [← BKM.variance_block d q hq ht _ hr, BKM.block_realPart, F.dual_realPart] at h1
  rw [← BKM.variance_block d q hq ht _ hi, BKM.block_imaginaryPart, F.dual_imaginaryPart] at h2
  have hh := add_le_add h1 h2
  rw [← mul_add, ← mul_add, BKM.variance_parts b p hp hs, BKM.variance_parts d q hq ht] at hh
  exact hh

end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J K L : Type*} [Fintype K] [DecidableEq K]
 theorem flow_complex_hessian (F : KrausFlow n) (τ : State n) (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1)
    (c a β ζ C : ℝ) (hc : 0 < c) (ha : 0 < a) (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (d : HilbertBasis (K ⊕ L) ℂ (Fock n)) (q : K ⊕ L → ℝ)
    (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hτ : FiniteEnergy τ)
    (hcross : ∀ σ, FiniteMoment 4 σ →
      Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) ((F.map σ).op (d j))).re))
    (hcτ : Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) (τ.op (d j))).re))
    (hlog : ∀ σ, FiniteMoment 4 σ → crossEntropy b p σ =
      (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d q (F.map σ)+(β/a)*energy σ+C)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-
        a*entropy ρ+β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-
        a*entropy σ+β*energy σ+ζ*numberMoment 4 σ)
    (Z : Matrix K K ℂ) :
    (1-κ)^2*BKM.variance b p (F.dual (FiniteBlock.block d Z)) ≤
      (a/c)*BKM.variance d q (FiniteBlock.block d Z) := by
  apply complex_component_hessian F c a κ b p hp hs.summable d q hq ht.summable
  intro T hT
  rw [BKM.variance, BKM.normSq_mean_selfAdjoint b p _
    (F.dual_selfAdjoint (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (FiniteBlock.block_symmetric d T hT))), mean_expectation ρ b p he]
  exact flow_full_hessian F τ κ hκ c a β ζ C hc ha ρ hmρ b p hp hs d q hq ht
    he he0 hτ hcross hcτ hlog hmin T hT
end EntropyPhotonNumber

namespace BKM
open scoped BigOperators
open DiagonalForms.System
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem mean_reindex (b : HilbertBasis J ℂ E) (p : J → ℝ) (e : I ≃ J) (Z : E →L[ℂ] E) :
    mean (reindexBasis b e) (p ∘ e) Z=mean b p Z := by
  simp only [mean, entry, reindexBasis_apply, Function.comp_def]
  exact e.tsum_eq (fun j : J => (p j : ℂ)*inner ℂ (b j) (Z (b j)))

theorem quadratic_reindex (b : HilbertBasis J ℂ E) (p : J → ℝ) (e : I ≃ J) (Z : E →L[ℂ] E) :
    quadratic (reindexBasis b e) (p ∘ e) Z=quadratic b p Z := by
  simp only [quadratic, entry, reindexBasis_apply, Function.comp_def]
  exact (Equiv.prodCongr e e).tsum_eq (fun ij : J × J => logMean (p ij.1) (p ij.2)*Complex.normSq (inner ℂ (b ij.1) (Z (b ij.2))))

theorem variance_reindex (b : HilbertBasis J ℂ E) (p : J → ℝ) (e : I ≃ J) (Z : E →L[ℂ] E) :
    variance (reindexBasis b e) (p ∘ e) Z=variance b p Z := by
  rw [variance, quadratic_reindex, mean_reindex, variance]
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

end

open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

end BKM

namespace CenteredTests
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
end CenteredTests

namespace EntropyPhotonNumber

section
open QuantumTrace DiagonalForms.System
variable {n : ℕ} {I J : Type*} [DecidableEq J]

end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J : Type*} [DecidableEq J]
theorem minimum_all_blocks_hessian_data
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
      ∀ (s : Finset J) (Z : Matrix s s ℂ),
      (1-κ)^2*BKM.variance G.basis (gibbsWeight G.eigenval)
        (F.dual (FiniteBlock.block (BKM.reindexBasis d (Equiv.sumCompl (· ∈ s))) Z)) ≤
      (a/c)*BKM.variance d q (FiniteBlock.block (BKM.reindexBasis d (Equiv.sumCompl (· ∈ s))) Z) := by
  classical
  obtain ⟨G,hG⟩ := flow_minimum_gibbs F τ hr hτ κ hκ hκ0 c a β ζ hc ha hβ hζ ρ hmρ
    d q hq ht he0 hmin
  let _ := G.nonempty
  let htκ : 1-κ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  let ρ0 := mixture (1-κ) htκ (F.map ρ) τ
  have hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ0.op := by
    rw [← hτ]
    exact mixture_replacement_le κ hκ (F.map ρ) τ
  have hfτ : FiniteEnergy τ := by simpa only [hτ] using thermalState_finiteEnergy n r hr
  have hcross (σ : State n) (hm : FiniteMoment 4 σ) :
      Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) ((F.map σ).op (d j))).re) :=
    crossEntropy_finite ρ0 (F.map σ) (F.finiteEnergy _ (finiteMoment_finiteEnergy (by norm_num) hm))
      hr hκ0 hκ.2 hle d q hq ht he0
  have hcτ := crossEntropy_finite ρ0 τ hfτ hr hκ0 hκ.2 hle d q hq ht he0
  have hα : 0 ≤ c*(1-κ)/a := div_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hκ.2)) ha.le
  have hlog (σ : State n) (hm : FiniteMoment 4 σ) :
      crossEntropy G.basis (gibbsWeight G.eigenval) σ =
        (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d q (F.map σ)+(β/a)*energy σ+
          Real.log (heatPartition G.eigenval) :=
    (G.crossEntropy_hamiltonian d q hq ht F hα (div_nonneg hβ ha.le) (div_pos hζ ha)
      hG σ hm (hcross σ hm)).tsum_eq
  refine ⟨G, hG, fun s Z => ?_⟩
  let e := Equiv.sumCompl (fun j => j ∈ s)
  let d' := BKM.reindexBasis d e
  have hq' : ∀ j, 0 < (q ∘ e) j := fun j => hq (e j)
  have ht' : HasSum (q ∘ e) 1 := e.hasSum_iff.mpr ht
  have he0' : ∀ j, (mixture (1-κ) htκ (F.map ρ) τ).op (d' j)=((q ∘ e) j:ℂ) • d' j := by
    intro j
    simpa only [d', BKM.reindexBasis_apply, Function.comp_def] using he0 (e j)
  have hcross' (σ : State n) (hm : FiniteMoment 4 σ) :
      Summable (fun j => (-Real.log ((q ∘ e) j))*(inner ℂ (d' j) ((F.map σ).op (d' j))).re) := by
    simpa only [d', BKM.reindexBasis_apply, Function.comp_def] using
      (hcross σ hm).comp_injective e.injective
  have hcτ' : Summable (fun j => (-Real.log ((q ∘ e) j))*(inner ℂ (d' j) (τ.op (d' j))).re) := by
    simpa only [d', BKM.reindexBasis_apply, Function.comp_def] using hcτ.comp_injective e.injective
  have hlog' (σ : State n) (hm : FiniteMoment 4 σ) :
      crossEntropy G.basis (gibbsWeight G.eigenval) σ =
        (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d' (q ∘ e) (F.map σ)+(β/a)*energy σ+
          Real.log (heatPartition G.eigenval) := by
    simpa only [d', crossEntropy_reindex] using hlog σ hm
  have hh := flow_complex_hessian F τ κ hκ c a β ζ (Real.log (heatPartition G.eigenval)) hc ha
    ρ hmρ G.basis (gibbsWeight G.eigenval) (gibbsWeight_pos G.eigenval G.heat)
    (gibbsWeight_hasSum G.eigenval G.heat) d' (q ∘ e) hq' ht' G.eigen he0' hfτ hcross' hcτ' hlog' hmin Z
  simpa only [d', BKM.variance_reindex] using hh

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

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber
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
open QuantumTrace DiagonalForms.System


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.minimum_all_blocks_hessian_data := @_root_.OAI.EntropyPhotonNumber.minimum_all_blocks_hessian_data
