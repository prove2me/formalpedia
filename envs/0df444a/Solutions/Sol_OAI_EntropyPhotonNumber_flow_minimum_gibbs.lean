-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.flow_minimum_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:10:32.531436+00:00
-- url     : https://prove2.me/submissions/5cf66efb-34be-49eb-be98-473bb7e173b3

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean:L698-L741
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.flow_minimum_gibbs. The node keeps its source
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
import Theorems.Thm_OAI_EntropyPhotonNumber_combined_form_representation
import Theorems.Thm_OAI_EntropyPhotonNumber_crossEntropy_finite
import Theorems.Thm_OAI_EntropyPhotonNumber_gibbs_slice_real_trace
import Theorems.Thm_OAI_EntropyPhotonNumber_logarithmic_slice_representation
import Theorems.Thm_OAI_QuantumTrace_cfc_apply_eigenvector
import Theorems.Thm_OAI_QuantumTrace_entropy_summable_and_le_crossEntropy
import Theorems.Thm_OAI_QuantumTrace_exists_positive_eigenbasis
import Theorems.Thm_OAI_QuantumTrace_gibbs_fock_spectral_regular
import Theorems.Thm_OAI_QuantumTrace_gibbs_high_moment_summable
import Theorems.Thm_OAI_QuantumTrace_hasSum_trace_basis
import Theorems.Thm_OAI_QuantumTrace_quantum_klein
import Theorems.Thm_OAI_QuantumTrace_spectral_gibbs_attains
import Theorems.Thm_OAI_QuantumTrace_weighted_number_moment

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
theorem diagonalMap_injective (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (hn : ∀ i, a i ≠ 0) : Function.Injective (diagonalMap a ha) := by
  intro x y h
  ext i
  exact mul_left_cancel₀ (hn i) (congrArg (fun z : SequenceHilbert ι => z i) h)

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

theorem basisDiagonal_positive (b : HilbertBasis ι ℂ E) (p : ι → ℝ)
    (hb : ∃ C : ℝ, ∀ i, ‖(p i : ℂ)‖ ≤ C) (hp : ∀ i, 0 ≤ p i) :
    (basisDiagonal b p hb).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  change ((inner ℂ (b.repr.symm (diagonalMap _ hb (b.repr x))) x).re : ℂ) = inner ℂ (b.repr.symm (diagonalMap _ hb (b.repr x))) x ∧
    0 ≤ (inner ℂ (b.repr.symm (diagonalMap _ hb (b.repr x))) x).re
  rw [b.repr.symm.inner_map_eq_flip]
  simp only [LinearIsometryEquiv.symm_symm]
  exact (ContinuousLinearMap.isPositive_iff_complex _).mp (diagonalMap_positive p hb hp) (b.repr x)

theorem basisDiagonal_injective (b : HilbertBasis ι ℂ E) (p : ι → ℝ)
    (hb : ∃ C : ℝ, ∀ i, ‖(p i : ℂ)‖ ≤ C) (hp : ∀ i, p i ≠ 0) :
    Function.Injective (basisDiagonal b p hb) :=
  b.repr.symm.injective.comp ((diagonalMap_injective _ hb (fun i =>
    Complex.ofReal_ne_zero.mpr (hp i))).comp b.repr.injective)

theorem basisDiagonal_hasSum_trace (b : HilbertBasis ι ℂ E) (p : ι → ℝ)
    (hb : ∃ C : ℝ, ∀ i, ‖(p i : ℂ)‖ ≤ C) {z : ℝ} (hp : HasSum p z) :
    HasSum (fun i => (inner ℂ (b i) (basisDiagonal b p hb (b i))).re) z := by
  convert hp using 1
  funext i
  rw [basisDiagonal_eigen, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  simp

theorem spectralGibbs_positive [Nonempty ι] (b : HilbertBasis ι ℂ E) (u : ι → ℝ)
    (hs : Summable (fun i => Real.exp (-u i))) : (spectralGibbs b u hs).IsPositive :=
  basisDiagonal_positive b _ _ (fun i => (gibbsWeight_pos u hs i).le)

theorem spectralGibbs_injective [Nonempty ι] (b : HilbertBasis ι ℂ E) (u : ι → ℝ)
    (hs : Summable (fun i => Real.exp (-u i))) : Function.Injective (spectralGibbs b u hs) :=
  basisDiagonal_injective b _ _ (fun i => (gibbsWeight_pos u hs i).ne')

theorem spectralGibbs_trace_one [CompleteSpace E] [Nonempty ι] (b : HilbertBasis ι ℂ E) (u : ι → ℝ)
    (hs : Summable (fun i => Real.exp (-u i))) {κ : Type*} (c : HilbertBasis κ ℂ E) :
    HasSum (fun j => (inner ℂ (c j) (spectralGibbs b u hs (c j))).re) 1 := by
  exact hasSum_trace_basis b c (spectralGibbs_positive b u hs)
    (basisDiagonal_hasSum_trace b _ _ (gibbsWeight_hasSum u hs))

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

theorem numberWeight_eq {n : ℕ} (i : NumberIndex n) :
    numberWeight i = 1+(totalNumber i : ℝ) := by
  simp only [numberWeight, totalNumber, Nat.cast_sum]

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

theorem sequenceBasis_numberKet {n : ℕ} (i : NumberIndex n) :
    sequenceBasis (NumberIndex n) i = numberKet i := by
  apply lp.ext
  funext j
  by_cases h : i = j
  · subst j; simp [sequenceBasis_apply, numberKet, lp.single_apply]
  · simp [sequenceBasis_apply, numberKet, lp.single_apply, h]

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

theorem spectral_gibbs_variational [Nonempty J] (a : HilbertBasis I ℂ E)
    (b : HilbertBasis J ℂ E) (u : J → ℝ)
    (hheat : Summable (fun j => Real.exp (-u j)))
    {T : E →L[ℂ] E} (hp : T.IsPositive)
    (ht : HasSum (fun i => (inner ℂ (a i) (T (a i))).re) 1)
    {S K : ℝ} (hS : HasSum (fun i => (inner ℂ (a i) (entropyOperator T (a i))).re) S)
    (hK : HasSum (fun j => u j*(inner ℂ (b j) (T (b j))).re) K) :
    -Real.log (heatPartition u) ≤ K-S ∧
      (K-S = -Real.log (heatPartition u) → T = spectralGibbs b u hheat) := by
  obtain ⟨L, c, p, hpp, hpt, heT⟩ := exists_positive_eigenbasis a hp ht
  have hSp := hasSum_entropy_eigenvalues a c hp ht p heT hS
  have ht' := hasSum_trace_basis a b hp ht
  have hcross : HasSum (fun j => (inner ℂ (b j) (T (b j))).re * (-Real.log (gibbsWeight u j)))
      (K+Real.log (heatPartition u)) := by
    have hh := hK.add (ht'.mul_right (Real.log (heatPartition u)))
    convert! hh using 1
    · funext j
      rw [log_gibbsWeight u hheat]
      ring
    · ring
  obtain ⟨hle, heq⟩ := quantum_klein c b (spectralGibbs_positive b u hheat).isSymmetric
    hpp hpt (gibbsWeight_pos u hheat) (gibbsWeight_hasSum u hheat)
    heT (spectralGibbs_eigen b u hheat) hSp hcross
  exact ⟨by linarith, fun hh => heq (by linarith)⟩

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

theorem spectralGibbs_seventh_moment
    (b : HilbertBasis J ℂ (SequenceHilbert (Fin n → ℕ))) (u : J → ℝ)
    (hu : ∀ j, 0 < u j) {k : ℝ} (hk : 0 < k)
    {B : SequenceHilbert (Fin n → ℕ) →L[ℂ] SequenceHilbert (Fin n → ℕ)}
    (hheat : Summable (fun j => Real.exp (-u j)))
    (hhalf : Summable (fun j => Real.exp (-(1/2 : ℝ)*u j)))
    (hreg : ∀ j, ∃ z : SequenceHilbert (Fin n → ℕ),
      (∀ i, z i = (rootNumberWeight i^7 : ℝ)*b j i) ∧
      ‖z‖ ≤ k⁻¹*(u j+‖B‖*Real.sqrt (u j/k))) :
    Summable (fun i => numberWeight i^7 *
      (inner ℂ (sequenceBasis _ i) (spectralGibbs b u hheat (sequenceBasis _ i))).re) := by
  choose z hz hzs using hreg
  have hn : Summable (fun j => Real.exp (-u j)*‖z j‖^2) :=
    gibbs_high_moment_summable u (fun j => (hu j).le) hk (norm_nonneg B)
      (fun j => ‖z j‖) (fun j => norm_nonneg _) hzs hhalf
  have hw : Summable (fun j => gibbsWeight u j*‖z j‖^2) := by
    apply (hn.div_const (heatPartition u)).congr
    intro j
    dsimp [gibbsWeight]
    ring
  apply weighted_number_moment b (spectralGibbs b u hheat) (gibbsWeight u)
    (fun j => (gibbsWeight_pos u hheat j).le) (spectralGibbs_eigen b u hheat)
    (fun i => numberWeight i^7) (fun i => pow_nonneg (by linarith [numberWeight_one_le i]) _)
    (fun j => ‖z j‖^2) _ hw
  intro j
  have heq : (fun i => ‖z j i‖^2) = (fun i => numberWeight i^7*‖b j i‖^2) := by
    funext i
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity [rootNumberWeight_one_le i]), mul_pow]
    congr 1
    rw [← pow_mul, show (7*2 : ℕ) = 2*7 from rfl, pow_mul, rootNumberWeight,
      Real.sq_sqrt (by linarith [numberWeight_one_le i])]
  rw [← heq]
  exact sequence_hasSum_norm_sq (z j)

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace
theorem exists_gibbs_state (n : ℕ) {k : ℝ} (hk : 0 < k)
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) :
    ∃ (J : Type) (_ : Nonempty J) (b : HilbertBasis J ℂ (Fock n)) (u : J → ℝ)
      (hheat : Summable (fun j => Real.exp (-u j))) (ω : State n),
      (∀ j, 0 < u j) ∧
      (∀ j, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (b j) =
        (((u j)⁻¹ : ℝ) : ℂ) • b j) ∧
      (∀ t : ℝ, 0 < t → Summable (fun j => Real.exp (-t*u j))) ∧
      ω.op = spectralGibbs b u hheat ∧ Function.Injective ω.op ∧ FiniteMoment 7 ω := by
  classical
  obtain ⟨J,b,u,hu,he,hreg,hheat⟩ := gibbs_fock_spectral_regular n hk hB
  have hJ : Nonempty J := by
    by_contra h
    have : IsEmpty J := not_nonempty_iff.mp h
    have hh := (basis_hasSum_norm_sq b (numberKet (fun _ : Fin n => 0))).tsum_eq
    simp only [tsum_empty] at hh
    have hn : ‖numberKet (fun _ : Fin n => 0)‖ = 1 := by simp [numberKet]
    rw [hn, one_pow] at hh
    exact zero_ne_one hh
  let _ := hJ
  have ht : Summable (fun j => Real.exp (-u j)) := by simpa using hheat 1 (by norm_num)
  let T := spectralGibbs b u ht
  have hT : T.IsPositive := spectralGibbs_positive b u ht
  have hs : HasSum (fun i => (entry T i i).re) 1 := by
    simpa only [sequenceBasis_numberKet, entry] using
      spectralGibbs_trace_one b u ht (sequenceBasis (NumberIndex n))
  let ω : State n := ⟨T,hT,hs⟩
  refine ⟨J,hJ,b,u,ht,ω,hu,he,hheat,rfl,spectralGibbs_injective b u ht,?_⟩
  have hm := spectralGibbs_seventh_moment b u hu hk ht (hheat (1/2) (by norm_num))
    (B := B) (fun j => by obtain ⟨y,z,_,hz,_,hzs⟩ := hreg j; exact ⟨z,hz,hzs⟩)
  simpa only [FiniteMoment, numberWeight_eq, sequenceBasis_numberKet, entry] using hm

end

section
open QuantumTrace TraceEnsemble

theorem sliced_gibbs_minimizer {n : ℕ} {K I : Type*}
    (a : HilbertBasis K ℂ (Fock n)) (w : K → ℝ) (hw : ∀ j, 0 ≤ w j)
    (V : I → Fock n →L[ℂ] Fock n) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Φ : State n → State n)
    (hΦ : ∀ (J : Type) (v : J → Fock n) (ρ : State n),
      HasSum (fun j => ‖v j‖^2) 1 → operator v = ρ.op →
      operator (fun z : I × J => V z.1 (v z.2)) = (Φ ρ).op)
    (hc : ∀ ρ, FiniteMoment 4 ρ →
      Summable (fun j => w j*(inner ℂ (a j) ((Φ ρ).op (a j))).re))
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re =
      ENNReal.ofReal α*sliceMoment a (fun j => ENNReal.ofReal (w j)) V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x))
    {k : ℝ} (hk : 0 < k) (ρ : State n) (hm : FiniteMoment 4 ρ)
    (hmin : ∀ σ, FiniteMoment 4 σ → sliceFreeEnergy a w Φ k α β ρ ≤ sliceFreeEnergy a w Φ k α β σ) :
    ∃ (J : Type) (_ : Nonempty J) (b : HilbertBasis J ℂ (Fock n)) (u : J → ℝ)
      (hheat : Summable (fun j => Real.exp (-u j))),
      (∀ j, 0 < u j) ∧
      (∀ j, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (b j) =
        (((u j)⁻¹ : ℝ) : ℂ) • b j) ∧
      ρ.op = spectralGibbs b u hheat ∧ Function.Injective ρ.op ∧ FiniteMoment 7 ρ := by
  classical
  obtain ⟨J,hJ,b,u,ht,ω,hu,he,hheat,hω,hinj,hmω⟩ := exists_gibbs_state n hk hB
  let _ := hJ
  have htrace (σ : State n) (hmσ : FiniteMoment 4 σ) :
      HasSum (fun j => u j*(inner ℂ (b j) (σ.op (b j))).re)
        (k*numberMoment 4 σ + α*(∑' j, w j*(inner ℂ (a j) ((Φ σ).op (a j))).re) + β*energy σ) := by
    obtain ⟨L,c,p,hp,hs,heσ⟩ := exists_positive_eigenbasis (numberBasis n)
      σ.positive (trace_one_numberBasis σ)
    have hv : HasSum (fun j => ‖diagonalVector c p j‖^2) 1 := by
      simpa only [diagonalVector_norm_sq c p hp] using hs
    exact gibbs_slice_real_trace b u hu c p hp hs σ heσ hmσ a w hw V hV (Φ σ)
      (hΦ L _ σ hv (diagonalVector_operator c p hp hs.summable σ.op heσ)) (hc σ hmσ)
      hB hα hβ hform hk he
  have hmω4 := finiteMoment_mono (by norm_num : 4 ≤ 7) hmω
  have htρ := htrace ρ hm
  have hVρ := spectral_gibbs_variational (numberBasis n) b u ht ρ.positive
    (trace_one_numberBasis ρ) (entropy_hasSum ρ (finiteMoment_finiteEnergy (by norm_num) hm)) htρ
  have hωatt := spectral_gibbs_attains (numberBasis n) b u (fun j => (hu j).le) ht
    (hheat (1/2) (by norm_num))
  have hSω : HasSum (fun i => (inner ℂ ((numberBasis n) i)
      (entropyOperator ω.op ((numberBasis n) i))).re) (entropy ω) :=
    entropy_hasSum ω (finiteMoment_finiteEnergy (by norm_num) hmω4)
  have hωeq : sliceFreeEnergy a w Φ k α β ω = -Real.log (heatPartition u) := by
    dsimp only at hωatt
    rw [← hω] at hωatt
    rw [(htrace ω hmω4).tsum_eq, hSω.tsum_eq] at hωatt
    exact hωatt.2.2
  have heq : sliceFreeEnergy a w Φ k α β ρ = -Real.log (heatPartition u) :=
    le_antisymm ((hmin ω hmω4).trans_eq hωeq) hVρ.1
  have hρop := hVρ.2 heq
  have hρω : ρ = ω := state_ext (hρop.trans hω.symm)
  exact ⟨J,hJ,b,u,ht,hu,he,hρop,by simpa only [hρω] using hinj,by simpa only [hρω] using hmω⟩

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

theorem one_port_majorant {n : ℕ} {J : Type*}
    (Φ : State n → State n) (τ : State n) (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1)
    (c a β ζ : ℝ) (hc : 0 < c) (ha : 0 < a)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (Φ ρ) τ).op (b j) =
      (p j : ℂ) • b j)
    (hfinite : ∀ σ, FiniteMoment 4 σ → FiniteEnergy (Φ σ)) (hτ : FiniteEnergy τ)
    (hcross : ∀ σ, FiniteMoment 4 σ →
      Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) ((Φ σ).op (b j))).re))
    (hcτ : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (τ.op (b j))).re))
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (Φ ρ) τ)-a*entropy ρ+
        β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (Φ σ) τ)-a*entropy σ+
        β*energy σ+ζ*numberMoment 4 σ) :
    ∀ σ, FiniteMoment 4 σ →
      sliceFreeEnergy b (fun j => -Real.log (p j)) Φ (ζ/a) (c*(1-κ)/a) (β/a) ρ ≤
      sliceFreeEnergy b (fun j => -Real.log (p j)) Φ (ζ/a) (c*(1-κ)/a) (β/a) σ := by
  let ht : 1-κ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  let ρ0 := mixture (1-κ) ht (Φ ρ) τ
  have hself := crossEntropy_self ρ0 (mixture_finiteEnergy _ _ (hfinite ρ hmρ) hτ) b p he
  have hmixρ := crossEntropy_mixture b p (1-κ) ht (Φ ρ) τ (hcross ρ hmρ) hcτ
  intro σ hmσ
  have hmixσ := crossEntropy_mixture b p (1-κ) ht (Φ σ) τ (hcross σ hmσ) hcτ
  have hcσ : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j)
      ((mixture (1-κ) ht (Φ σ) τ).op (b j))).re) := by
    convert! ((hcross σ hmσ).mul_left (1-κ)).add (hcτ.mul_left (1-(1-κ))) using 1
    funext j
    simp only [mixture, add_apply, smul_apply, inner_add_right, inner_smul_right,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hmaj := (entropy_le_crossEntropy ρ0 (mixture (1-κ) ht (Φ σ) τ)
    (mixture_finiteEnergy _ _ (hfinite σ hmσ) hτ) b p hp hs he hcσ).1
  have hm := hmin σ hmσ
  have hρeq : c*entropy ρ0 = c*((1-κ)*crossEntropy b p (Φ ρ)+κ*crossEntropy b p τ) := by
    rw [← hself, hmixρ]
    congr 1
    ring
  have hσle : c*entropy (mixture (1-κ) ht (Φ σ) τ) ≤
      c*((1-κ)*crossEntropy b p (Φ σ)+κ*crossEntropy b p τ) := by
    have hh := mul_le_mul_of_nonneg_left hmaj hc.le
    rw [hmixσ] at hh
    simpa only [show 1-(1-κ) = κ by ring] using hh
  apply (mul_le_mul_iff_right₀ ha).mp
  have hscale (x : State n) :
      a*sliceFreeEnergy b (fun j => -Real.log (p j)) Φ (ζ/a) (c*(1-κ)/a) (β/a) x =
      ζ*numberMoment 4 x+c*(1-κ)*crossEntropy b p (Φ x)+β*energy x-a*entropy x := by
    dsimp [sliceFreeEnergy, crossEntropy]
    field_simp
  rw [hscale, hscale]
  change c*entropy ρ0-a*entropy ρ+β*energy ρ+ζ*numberMoment 4 ρ ≤ _ at hm
  rw [hρeq] at hm
  linarith

end

section
open QuantumTrace TensorLp

namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end

section
open QuantumTrace
theorem flow_minimum_gibbs {n : ℕ} {J : Type*}
    (F : KrausFlow n) (τ : State n) {r : ℝ} (hr : 0 < r) (hτ : τ = thermalState n r hr)
    (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1) (hκ0 : 0 < κ)
    (c a β ζ : ℝ) (hc : 0 < c) (ha : 0 < a) (hβ : 0 ≤ β) (hζ : 0 < ζ)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (b j) =
      (p j : ℂ) • b j)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-a*entropy ρ+
        β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-a*entropy σ+
        β*energy σ+ζ*numberMoment 4 σ) :
    ∃ G : GibbsData n (ζ/a) ρ, ∀ x,
      ENNReal.ofReal (inner ℂ x (G.B x)).re =
        ENNReal.ofReal (c*(1-κ)/a)*
          sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) F.V (energyInverse n x)+
        ENNReal.ofReal (β/a)*numberVectorMoment (energyInverse n x) := by
  let ht : 1-κ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  let ρ0 := mixture (1-κ) ht (F.map ρ) τ
  have hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ0.op := by
    rw [← hτ]
    exact mixture_replacement_le κ hκ (F.map ρ) τ
  have hf (σ : State n) (hm : FiniteMoment 4 σ) : FiniteEnergy (F.map σ) :=
    F.finiteEnergy σ (finiteMoment_finiteEnergy (by norm_num) hm)
  have hfτ : FiniteEnergy τ := by simpa only [hτ] using thermalState_finiteEnergy n r hr
  have hcross (σ : State n) (hm : FiniteMoment 4 σ) :
      Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) ((F.map σ).op (b j))).re) :=
    crossEntropy_finite ρ0 (F.map σ) (hf σ hm) hr hκ0 hκ.2 hle b p hp hs he
  have hcτ := crossEntropy_finite ρ0 τ hfτ hr hκ0 hκ.2 hle b p hp hs he
  have hα : 0 ≤ c*(1-κ)/a := div_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hκ.2)) ha.le
  have hβ' : 0 ≤ β/a := div_nonneg hβ ha.le
  have hk : 0 < ζ/a := div_pos hζ ha
  have hw (j : J) : 0 ≤ -Real.log (p j) := neg_nonneg.mpr (Real.log_nonpos (hp j).le
    (hs.tsum_eq ▸ hs.summable.le_tsum j (fun i _ => (hp i).le)))
  obtain ⟨B,hB,hform⟩ := logarithmic_slice_representation ρ0 hr hκ0 hκ.2 hle b p hp hs he
    F.V F.F F.nonneg F.norm F.energy
  obtain ⟨C,hC,hCform⟩ := combined_form_representation b
    (fun j => ENNReal.ofReal (-Real.log (p j))) F.V hB hform hα hβ'
  have hm := one_port_majorant F.map τ κ hκ c a β ζ hc ha ρ hmρ b p hp hs he hf hfτ hcross hcτ hmin
  obtain ⟨L,hL,d,u,heat,hu,hinv,hop,hinj,hm7⟩ := sliced_gibbs_minimizer b
    (fun j => -Real.log (p j)) hw F.V F.norm F.map F.ensemble hcross hC hα hβ' hCform hk ρ hmρ hm
  let G : GibbsData n (ζ/a) ρ := ⟨C,hC,L,hL,d,u,hu,heat,hinv,hop,hinj,hm7⟩
  exact ⟨G,hCform⟩

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
open QuantumTrace


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.flow_minimum_gibbs := @_root_.OAI.EntropyPhotonNumber.flow_minimum_gibbs
