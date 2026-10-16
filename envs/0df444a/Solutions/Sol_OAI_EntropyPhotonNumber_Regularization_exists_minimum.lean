-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.Regularization.exists_minimum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:46:43.669001+00:00
-- url     : https://prove2.me/submissions/6b2ba393-1156-4698-8b2a-fe4418a5cd0d

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean:L1508-L1525
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.Regularization.exists_minimum. The node keeps its source
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
import Theorems.Thm_OAI_EntropyPhotonNumber_Regularization_sublevel_bounds
import Theorems.Thm_OAI_EntropyPhotonNumber_regularizedOutput_energy_bound
import Theorems.Thm_OAI_QuantumTrace_cfc_apply_eigenvector
import Theorems.Thm_OAI_QuantumTrace_energySet_limit
import Theorems.Thm_OAI_QuantumTrace_energySet_totallyBounded
import Theorems.Thm_OAI_QuantumTrace_entropy_small_mass_bound
import Theorems.Thm_OAI_QuantumTrace_entropy_summable_and_le_crossEntropy
import Theorems.Thm_OAI_QuantumTrace_exists_positive_eigenbasis
import Theorems.Thm_OAI_QuantumTrace_tendsto_tsum_of_uniform_tail

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

end

open QuantumTrace Annihilation
variable {n : ℕ}

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

theorem numberBox_compl_weight {n K : ℕ} {k : Fin n → ℕ}
    (hk : k ∉ numberBox n K) : (K + 1 : ℝ) ≤ ∑ j, (k j : ℝ) := by
  classical
  simp only [numberBox, Fintype.mem_piFinset, Finset.mem_range, not_forall] at hk
  obtain ⟨j, hj⟩ := hk
  have hh : K + 1 ≤ k j := Nat.le_of_not_gt hj
  have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => Nat.zero_le (k i))
    (Finset.mem_univ j)
  exact_mod_cast hh.trans hs

theorem number_tail_mass_le {n K : ℕ} (p : (Fin n → ℕ) → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hs : Summable p)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * p k)) :
    (∑' k : {k // k ∉ numberBox n K}, p k) ≤
      (∑' k, (∑ j, (k j : ℝ)) * p k) / (K + 1) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < K + 1)]
  rw [← tsum_mul_right]
  calc
    _ ≤ ∑' k : {k // k ∉ numberBox n K}, (∑ j, ((k : Fin n → ℕ) j : ℝ)) * p k := by
      apply ((hs.subtype _).mul_right _).tsum_le_tsum _ (hE.subtype _)
      intro k
      change p k * (K + 1) ≤ (∑ j, ((k : Fin n → ℕ) j : ℝ)) * p k
      nlinarith [numberBox_compl_weight k.property, hp k]
    _ ≤ _ := Summable.tsum_subtype_le _ _ (fun k => mul_nonneg
      (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (hp k)) hE

theorem entropy_tail_le_modulus {n : ℕ} (p : (Fin n → ℕ) → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hpu : ∀ k, p k ≤ 1) (hs : Summable p)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * p k))
    (s : Finset (Fin n → ℕ)) {E : ℝ}
    (hEb : (∑' k, (∑ j, (k j : ℝ)) * p k) ≤ E) :
    let q := ∑' k : {k // k ∉ s}, p k
    (∑' k : {k // k ∉ s}, Real.negMulLog (p k)) ≤
      (n + 1 : ℝ) * Real.negMulLog q + n * q ^ 2 + E * q := by
  classical
  let a : (Fin n → ℕ) → ℝ := fun k => if k ∈ s then 0 else p k
  have ha : ∀ k, 0 ≤ a k := fun k => by dsimp [a]; split_ifs <;> first | exact le_refl _ | exact hp k
  have hau : ∀ k, a k ≤ 1 := fun k => by dsimp [a]; split_ifs <;> first | linarith | exact hpu k
  have has : Summable a := hs.of_nonneg_of_le ha (fun k => by dsimp [a]; split_ifs <;> simp_all)
  have hae : Summable (fun k => (∑ j, (k j : ℝ)) * a k) := by
    apply hE.of_nonneg_of_le (fun k => mul_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (ha k))
    intro k
    dsimp [a]; split_ifs
    · simp only [mul_zero]
      exact mul_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (hp k)
    · exact le_refl _
  have haq : (∑' k, a k) = ∑' k : {k // k ∉ s}, p k := by
    convert (tsum_subtype {k | k ∉ s} p).symm using 1
    · congr 1; ext k; simp [a, Set.indicator_apply]
    · rfl
  have haentropy : (∑' k, Real.negMulLog (a k)) =
      ∑' k : {k // k ∉ s}, Real.negMulLog (p k) := by
    convert (tsum_subtype {k | k ∉ s} (fun k => Real.negMulLog (p k))).symm using 1
    · congr 1; ext k; by_cases hk : k ∈ s <;> simp [a, hk]
    · rfl
  have hh := (entropy_small_mass_bound a ha hau has.hasSum hae).2
  rw [haq, haentropy] at hh
  apply hh.trans
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right _ (tsum_nonneg (fun k : {k // k ∉ s} => hp k))
  apply le_trans _ hEb
  apply hae.tsum_le_tsum _ hE
  intro k
  dsimp [a]; split_ifs
  · simp only [mul_zero]
    exact mul_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (hp k)
  · exact le_refl _

theorem entropy_uniform_tail {n : ℕ} {E ε : ℝ} (_hE0 : 0 ≤ E) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ (p : (Fin n → ℕ) → ℝ), (∀ k, 0 ≤ p k) →
      (∀ k, p k ≤ 1) → Summable p →
      Summable (fun k => (∑ j, (k j : ℝ)) * p k) →
      (∑' k, (∑ j, (k j : ℝ)) * p k) ≤ E →
      (∑' k : {k // k ∉ numberBox n K}, Real.negMulLog (p k)) < ε := by
  let M : ℝ → ℝ := fun q => (n + 1 : ℝ) * Real.negMulLog q + n * q ^ 2 + E * q
  have hm : ContinuousAt M 0 := by fun_prop
  have hm0 : M 0 = 0 := by simp [M]
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hm ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (E / δ)
  refine ⟨K, ?_⟩
  intro p hp hpu hs hEs hEb
  let q := ∑' k : {k // k ∉ numberBox n K}, p k
  have hq0 : 0 ≤ q := tsum_nonneg (fun k => hp k)
  have hqle : q ≤ E / (K + 1) :=
    (number_tail_mass_le p hp hs hEs).trans (div_le_div_of_nonneg_right hEb (by positivity))
  have hqδ : q < δ := by
    have hkδ : E < K * δ := (div_lt_iff₀ hδ).mp hK
    apply hqle.trans_lt
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < K + 1)]
    nlinarith
  have hh := hd (show dist q 0 < δ by simpa [Real.dist_eq, abs_of_nonneg hq0] using hqδ)
  rw [hm0, dist_zero_right, Real.norm_eq_abs] at hh
  exact (entropy_tail_le_modulus p hp hpu hs hEs _ hEb).trans_lt ((le_abs_self _).trans_lt hh)

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

omit [CompleteSpace H] in
theorem diagonal_le_one (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H}
    (hp : T.IsPositive) (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) 1)
    (i : ι) : (inner ℂ (b i) (T (b i))).re ≤ 1 := by
  simpa only [ht.tsum_eq] using ht.summable.le_tsum i (fun j _ => hp.re_inner_nonneg_right (b j))

theorem entropyOperator_tendsto {α : Type*} {l : Filter α}
    {T : α → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hp : ∀ a, (T a).IsPositive) (hA : A.IsPositive)
    (hn : ∀ a, ‖T a‖ ≤ 1) (hnA : ‖A‖ ≤ 1)
    (ht : Tendsto T l (𝓝 A)) :
    Tendsto (fun a => entropyOperator (T a)) l (𝓝 (entropyOperator A)) := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · have : Subsingleton H := hH
    have he : (fun a => entropyOperator (T a)) = fun _ => entropyOperator A :=
      funext (fun a => Subsingleton.elim _ _)
    rw [he]
    exact tendsto_const_nhds
  have : Nontrivial H := hH
  have hspec (B : H →L[ℂ] H) (hB : B.IsPositive) (hBn : ‖B‖ ≤ 1) :
      spectrum ℝ B ⊆ Set.Icc 0 1 := by
    intro x hx
    exact ⟨spectrum_nonneg_of_nonneg ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hB) hx,
      (Real.le_norm_self _).trans ((spectrum.norm_le_norm_of_mem hx).trans hBn)⟩
  exact Tendsto.cfc isCompact_Icc Real.negMulLog ht
    (Eventually.of_forall (fun a => hspec _ (hp a) (hn a)))
    (Eventually.of_forall (fun a => (hp a).isSymmetric.isSelfAdjoint))
    (hspec _ hA hnA) hA.isSymmetric.isSelfAdjoint Real.continuous_negMulLog.continuousOn

theorem entropy_tendsto_finite_energy {α : Type*} {l : Filter α} {n : ℕ}
    (b : HilbertBasis (Fin n → ℕ) ℂ H) {T : α → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hp : ∀ a, (T a).IsPositive) (hA : A.IsPositive)
    (ht : ∀ a, HasSum (fun k => (inner ℂ (b k) (T a (b k))).re) 1)
    (htA : HasSum (fun k => (inner ℂ (b k) (A (b k))).re) 1)
    (hEs : ∀ a, Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T a (b k))).re))
    (hEsA : Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (b k) (A (b k))).re))
    {E : ℝ} (hEb : ∀ a, (∑' k, (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T a (b k))).re) ≤ E)
    (hEbA : (∑' k, (∑ j, (k j : ℝ)) * (inner ℂ (b k) (A (b k))).re) ≤ E)
    (hlim : Tendsto T l (𝓝 A)) :
    Tendsto (fun a => ∑' k, (inner ℂ (b k) (entropyOperator (T a) (b k))).re) l
      (𝓝 (∑' k, (inner ℂ (b k) (entropyOperator A (b k))).re)) := by
  have hn (a : α) := norm_le_trace b (hp a) (ht a)
  have hnA := norm_le_trace b hA htA
  have hepos (a : α) := entropyOperator_positive (hp a) (hn a)
  have heA := entropyOperator_positive hA hnA
  apply tendsto_tsum_of_uniform_tail
    (fun a => entropy_summable_finite_energy b (hp a) (ht a) (hEs a))
    (entropy_summable_finite_energy b hA htA hEsA)
    (fun a k => (hepos a).re_inner_nonneg_right (b k))
    (fun k => heA.re_inner_nonneg_right (b k))
  · intro k
    have hh := entropyOperator_tendsto hp hA hn hnA hlim
    have heval : Continuous (fun B : H →L[ℂ] H => B (b k)) :=
      continuous_id.clm_apply continuous_const
    have hx := heval.continuousAt.tendsto.comp hh
    exact Complex.continuous_re.continuousAt.tendsto.comp (tendsto_const_nhds.inner hx)
  · intro ε hε
    have hE0 : 0 ≤ E := (tsum_nonneg (fun k => mul_nonneg
      (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (hA.re_inner_nonneg_right (b k)))).trans hEbA
    obtain ⟨K, hK⟩ := entropy_uniform_tail (n := n) hE0 hε
    refine ⟨numberBox n K, ?_, ?_⟩
    · intro a
      have hpd (k : Fin n → ℕ) := (hp a).re_inner_nonneg_right (b k)
      have hpu (k : Fin n → ℕ) := diagonal_le_one b (hp a) (ht a) k
      have hes := (entropy_small_mass_bound _ hpd hpu (ht a) (hEs a)).1
      apply lt_of_le_of_lt _ (hK _ hpd hpu (ht a).summable (hEs a) (hEb a))
      apply ((entropy_summable_finite_energy b (hp a) (ht a) (hEs a)).subtype _).tsum_le_tsum _ (hes.subtype _)
      intro k
      exact entropyOperator_quadratic_le b (hp a) (ht a) (b k) (b.orthonormal.norm_eq_one k)
    · have hpd (k : Fin n → ℕ) := hA.re_inner_nonneg_right (b k)
      have hpu (k : Fin n → ℕ) := diagonal_le_one b hA htA k
      have hes := (entropy_small_mass_bound _ hpd hpu htA hEsA).1
      apply lt_of_le_of_lt _ (hK _ hpd hpu htA.summable hEsA hEbA)
      apply ((entropy_summable_finite_energy b hA htA hEsA).subtype _).tsum_le_tsum _ (hes.subtype _)
      intro k
      exact entropyOperator_quadratic_le b hA htA (b k) (b.orthonormal.norm_eq_one k)

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open Filter Topology

theorem tsum_bound_of_tendsto {α ι : Type*} {l : Filter α} [NeBot l]
    {f : α → ι → ℝ} {g : ι → ℝ} {C : ℝ}
    (hfp : ∀ a i, 0 ≤ f a i) (hfs : ∀ a, Summable (f a))
    (hfb : ∀ a, (∑' i, f a i) ≤ C)
    (hlim : ∀ i, Tendsto (fun a => f a i) l (𝓝 (g i))) :
    Summable g ∧ (∑' i, g i) ≤ C := by
  have hg : ∀ i, 0 ≤ g i := fun i => ge_of_tendsto (hlim i) (Eventually.of_forall (fun a => hfp a i))
  have hs : ∀ s : Finset ι, (∑ i ∈ s, g i) ≤ C := by
    intro s
    apply le_of_tendsto (tendsto_finsetSum s (fun i _ => hlim i))
    exact Eventually.of_forall (fun a => ((hfs a).sum_le_tsum s (fun i _ => hfp a i)).trans (hfb a))
  exact ⟨summable_of_sum_le hg hs, Real.tsum_le_of_sum_le hg hs⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

theorem energySet_isClosed {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H) (E : ℝ) :
    IsClosed (energySet b E) := by
  apply IsSeqClosed.isClosed
  intro T A hT hlim
  exact energySet_limit b hT hlim

end

section
open ContinuousLinearMap Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem energySet_isCompact {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H) (E : ℝ) :
    IsCompact (energySet b E) :=
  (energySet_totallyBounded b E).isCompact_of_isClosed (energySet_isClosed b E)

end

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem momentSet_limit {α : Type*} {l : Filter α} [NeBot l] {n : ℕ}
    (b : HilbertBasis (Fin n → ℕ) ℂ H) {w : (Fin n → ℕ) → ℝ}
    (hw : ∀ k, 0 ≤ w k) {E M : ℝ}
    {T : α → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hT : ∀ a, T a ∈ momentSet b w E M) (hlim : Tendsto T l (𝓝 A)) :
    A ∈ momentSet b w E M := by
  refine ⟨energySet_limit b (fun a => (hT a).1) hlim, ?_⟩
  apply tsum_bound_of_tendsto (l := l)
    (fun a k => mul_nonneg (hw k) ((hT a).1.1.re_inner_nonneg_right (b k)))
    (fun a => (hT a).2.1) (fun a => (hT a).2.2)
  intro k
  have heval : Continuous (fun B : H →L[ℂ] H => B (b k)) :=
    continuous_id.clm_apply continuous_const
  exact tendsto_const_nhds.mul (Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_const_nhds.inner (heval.continuousAt.tendsto.comp hlim)))

theorem momentSet_isCompact {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H)
    (w : (Fin n → ℕ) → ℝ) (hw : ∀ k, 0 ≤ w k) (E M : ℝ) :
    IsCompact (momentSet b w E M) := by
  have hc : IsClosed (momentSet b w E M) := by
    apply IsSeqClosed.isClosed
    intro T A hT hlim
    exact momentSet_limit b hw hT hlim
  exact (energySet_isCompact b E).of_isClosed_subset hc (fun _ h => h.1)

theorem lowerSemicontinuous_tsum_nonneg {A I : Type*} [TopologicalSpace A]
    (f : A → I → ℝ) (hp : ∀ a i, 0 ≤ f a i) (hs : ∀ a, Summable (f a))
    (hc : ∀ i, Continuous (fun a => f a i)) :
    LowerSemicontinuous (fun a => ∑' i, f a i) := by
  intro a y hy
  obtain ⟨F, hF⟩ := ((hs a).hasSum.eventually (eventually_gt_nhds hy)).exists
  have ch : Continuous (fun x => ∑ i ∈ F, f x i) :=
    continuous_finsetSum F (fun i _ => hc i)
  filter_upwards [ch.continuousAt.eventually (eventually_gt_nhds hF)] with x hx
  exact hx.trans_le ((hs x).sum_le_tsum F (fun i _ => hp x i))

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

theorem norm_tail_le {f : I → G} {s : ℝ} (hf : HasSum (fun i => ‖f i‖) s)
    (F : Finset I) : ‖(∑' i, f i) - ∑ i ∈ F, f i‖ ≤ s - ∑ i ∈ F, ‖f i‖ := by
  classical
  have h₁ := hf.summable.of_norm.sum_add_tsum_compl (s := F)
  have h₂ := hf.summable.sum_add_tsum_compl (s := F)
  rw [hf.tsum_eq] at h₂
  have e₁ : (∑' i, f i) - ∑ i ∈ F, f i = ∑' i : ↥((↑F : Set I)ᶜ), f i := by
    rw [← h₁]; abel
  have e₂ : s - ∑ i ∈ F, ‖f i‖ = ∑' i : ↥((↑F : Set I)ᶜ), ‖f i‖ := by
    rw [← h₂]; ring
  rw [e₁,e₂]
  exact norm_tsum_le_tsum_norm (hf.summable.subtype _)

theorem tendsto_tsum_fixed_norm {l : Filter A} {f : A → I → G} {g : I → G} {s : ℝ}
    (hf : ∀ a, HasSum (fun i => ‖f a i‖) s) (hg : HasSum (fun i => ‖g i‖) s)
    (hfg : ∀ i, Tendsto (fun a => f a i) l (𝓝 (g i))) :
    Tendsto (fun a => ∑' i, f a i) l (𝓝 (∑' i, g i)) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨F, hF⟩ : ∃ F : Finset I, dist (∑ i ∈ F, ‖g i‖) s < ε/4 :=
    ((Metric.tendsto_nhds.mp hg) (ε/4) (by positivity)).exists
  have hsF : s - ∑ i ∈ F, ‖g i‖ < ε/4 := by
    exact (le_abs_self _).trans_lt (by simpa [Real.dist_eq, abs_sub_comm] using hF)
  have hhead := tendsto_finsetSum F (fun i _ => hfg i)
  have hmass := tendsto_finsetSum F (fun i _ => (hfg i).norm)
  filter_upwards [(Metric.tendsto_nhds.mp hhead) (ε/4) (by positivity),
    (Metric.tendsto_nhds.mp hmass) (ε/4) (by positivity)] with a ha hm
  have hmass' : (∑ i ∈ F, ‖g i‖) - ∑ i ∈ F, ‖f a i‖ < ε/4 :=
    (le_abs_self _).trans_lt (by simpa [Real.dist_eq, abs_sub_comm] using hm)
  rw [dist_eq_norm]
  calc
    _ ≤ ‖(∑' i, f a i) - ∑ i ∈ F, f a i‖ +
        ‖(∑ i ∈ F, f a i) - ∑ i ∈ F, g i‖ +
        ‖(∑' i, g i) - ∑ i ∈ F, g i‖ := by
      simpa [norm_sub_rev, add_assoc] using
        (norm_sub_le_norm_sub_add_norm_sub (∑' i, f a i)
          (∑ i ∈ F, f a i) (∑' i, g i)).trans
          (add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub
            (∑ i ∈ F, f a i) (∑ i ∈ F, g i) (∑' i, g i)))
    _ ≤ (s - ∑ i ∈ F, ‖f a i‖) + ‖(∑ i ∈ F, f a i) - ∑ i ∈ F, g i‖ +
        (s - ∑ i ∈ F, ‖g i‖) :=
      add_le_add (add_le_add (norm_tail_le (hf a) F) le_rfl) (norm_tail_le hg F)
    _ < ε := by rw [dist_eq_norm] at ha; linarith

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem tendsto_operator {l : Filter A} {v : A → I → E} {w : I → E} {s : ℝ}
    (hv : ∀ a, HasSum (fun i => ‖v a i‖^2) s) (hw : HasSum (fun i => ‖w i‖^2) s)
    (hvw : ∀ i, Tendsto (fun a => v a i) l (𝓝 (w i))) :
    Tendsto (fun a => operator (v a)) l (𝓝 (operator w)) := by
  apply tendsto_tsum_fixed_norm (s := s)
  · intro a
    simpa only [InnerProductSpace.norm_rankOne, pow_two] using hv a
  · simpa only [InnerProductSpace.norm_rankOne, pow_two] using hw
  · intro i
    have hc : Continuous (fun x : E => InnerProductSpace.rankOne ℂ x x) := by
      simp only [InnerProductSpace.rankOne_def]
      exact ((ContinuousLinearMap.smulRightL ℂ E E).continuous.comp
        (innerSL ℂ).continuous).clm_apply continuous_id
    exact (hc.tendsto _).comp (hvw i)

theorem tendsto_positiveRoot {l : Filter A} {T : A → E →L[ℂ] E} {R : E →L[ℂ] E}
    (hT : ∀ a, (T a).IsPositive) (hR : R.IsPositive)
    (h : Tendsto T l (𝓝 R)) : Tendsto (fun a => positiveRoot (T a)) l (𝓝 (positiveRoot R)) := by
  apply (CFC.continuousOn_sqrt.continuousWithinAt
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hR)).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨h, Filter.Eventually.of_forall (fun a =>
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (hT a))⟩

end TraceEnsemble

namespace TensorLp
variable {A B : Type*}

theorem tendsto_tensor {C : Type*} {l : Filter C} {x : C → H A} {y : C → H B}
    {a : H A} {b : H B} (hx : Filter.Tendsto x l (nhds a)) (hy : Filter.Tendsto y l (nhds b)) :
    Filter.Tendsto (fun c => tensor (x c) (y c)) l (nhds (tensor a b)) :=
  (tensorBilinear.continuous₂.tendsto (a,b)).comp (hx.prodMk_nhds hy)

end TensorLp

namespace EntropyPhotonNumber

section
open Filter Topology TensorLp

theorem tendsto_rootColumn {n : ℕ} {A : Type*} {l : Filter A}
    {ρ : A → State n} {σ : State n}
    (h : Tendsto (fun a => (ρ a).op) l (𝓝 σ.op)) (k : NumberIndex n) :
    Tendsto (fun a => rootColumn (ρ a) k) l (𝓝 (rootColumn σ k)) :=
  (ContinuousLinearMap.apply ℂ (Fock n) (numberKet k)).continuous.tendsto _ |>.comp
    (TraceEnsemble.tendsto_positiveRoot (fun a => (ρ a).positive) σ.positive h)

theorem tendsto_beamOutput {n : ℕ} {A : Type*} {l : Filter A}
    (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    {ρ σ : A → State n} {ρ₀ σ₀ : State n}
    (hρ : Tendsto (fun a => (ρ a).op) l (𝓝 ρ₀.op))
    (hσ : Tendsto (fun a => (σ a).op) l (𝓝 σ₀.op)) :
    Tendsto (fun a => (beamOutput η hη (ρ a) (σ a)).op) l (𝓝 (beamOutput η hη ρ₀ σ₀).op) := by
  apply TraceEnsemble.tendsto_operator
    (fun a => hasSum_slice_family (mixedVector_norm η hη (ρ a) (σ a)))
    (hasSum_slice_family (mixedVector_norm η hη ρ₀ σ₀))
  intro bi
  apply (sliceCLM bi.1).continuous.tendsto _ |>.comp
  apply (beamUnitary η hη).continuous.tendsto _ |>.comp
  exact tendsto_tensor (tendsto_rootColumn hρ bi.2.1) (tendsto_rootColumn hσ bi.2.2)

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

theorem regularizedOutput_finiteEnergy {n : ℕ} (η δ κ : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hδ : δ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1) {τD τ0 ρ σ : State n}
    (hD : FiniteEnergy τD) (h0 : FiniteEnergy τ0) (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    FiniteEnergy (regularizedOutput η δ κ hη hδ hκ τD τ0 ρ σ) :=
  mixture_finiteEnergy _ _ (beamOutput_finiteEnergy _ _ (beamOutput_finiteEnergy _ _ hρ hσ) hD) h0

theorem tendsto_regularizedOutput {n : ℕ} {A : Type*} {l : Filter A}
    (η δ κ : ℝ) (hη : η ∈ Set.Icc 0 1) (hδ : δ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1)
    (τD τ0 : State n) {ρ σ : A → State n} {ρ₀ σ₀ : State n}
    (hρ : Tendsto (fun a => (ρ a).op) l (𝓝 ρ₀.op))
    (hσ : Tendsto (fun a => (σ a).op) l (𝓝 σ₀.op)) :
    Tendsto (fun a => (regularizedOutput η δ κ hη hδ hκ τD τ0 (ρ a) (σ a)).op) l
      (𝓝 (regularizedOutput η δ κ hη hδ hκ τD τ0 ρ₀ σ₀).op) := by
  exact ((tendsto_const_nhds.smul (tendsto_beamOutput _ _
    (tendsto_beamOutput _ _ hρ hσ) tendsto_const_nhds)).add tendsto_const_nhds)

theorem tendsto_entropy {n : ℕ} {A : Type*} {l : Filter A} {ρ : A → State n} {σ : State n}
    {E : ℝ} (hρ : ∀ a, FiniteEnergy (ρ a)) (hσ : FiniteEnergy σ)
    (hb : ∀ a, energy (ρ a) ≤ E) (hc : energy σ ≤ E)
    (h : Tendsto (fun a => (ρ a).op) l (𝓝 σ.op)) :
    Tendsto (fun a => entropy (ρ a)) l (𝓝 (entropy σ)) := by
  simp only [entropy_eq_quantumTrace]
  apply entropy_tendsto_finite_energy (E := E) (numberBasis n) (fun a => (ρ a).positive) σ.positive
    (fun a => trace_one_numberBasis (ρ a)) (trace_one_numberBasis σ) _ _ _ _ h
  · simpa only [FiniteEnergy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using hρ
  · simpa only [FiniteEnergy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using hσ
  · simpa only [energy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using hb
  · simpa only [energy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using hc

theorem continuous_state_op (n : ℕ) : Continuous (State.op : State n → Fock n →L[ℂ] Fock n) :=
  continuous_induced_dom

theorem State.ext_op {n : ℕ} {ρ σ : State n} (h : ρ.op = σ.op) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

theorem stateOfMomentSet_mem {n : ℕ} {E M : ℝ}
    (T : momentSet (numberBasis n) (fun k => (1+(totalNumber k : ℝ))^4) E M) :
    stateOfMomentSet T ∈ boundedStates n E M := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [FiniteEnergy, totalNumber, Nat.cast_sum, entry, numberBasis_apply,
      stateOfMomentSet] using T.property.1.2.2.1
  · simpa only [energy, totalNumber, Nat.cast_sum, entry, numberBasis_apply,
      stateOfMomentSet] using T.property.1.2.2.2
  · simpa only [FiniteMoment, entry, numberBasis_apply, stateOfMomentSet] using T.property.2.1
  · simpa only [numberMoment, entry, numberBasis_apply, stateOfMomentSet] using T.property.2.2

theorem op_mem_momentSet {n : ℕ} {E M : ℝ} {ρ : State n} (hρ : ρ ∈ boundedStates n E M) :
    ρ.op ∈ momentSet (numberBasis n) (fun k => (1+(totalNumber k : ℝ))^4) E M := by
  refine ⟨⟨ρ.positive, trace_one_numberBasis ρ, ?_, ?_⟩, ?_, ?_⟩
  · simpa only [FiniteEnergy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using hρ.1
  · simpa only [energy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using hρ.2.1
  · simpa only [FiniteMoment, entry, numberBasis_apply] using hρ.2.2.1
  · simpa only [numberMoment, entry, numberBasis_apply] using hρ.2.2.2

theorem boundedStates_isCompact (n : ℕ) (E M : ℝ) : IsCompact (boundedStates n E M) := by
  let S := momentSet (numberBasis n) (fun k => (1+(totalNumber k : ℝ))^4) E M
  have hc : IsCompact S := momentSet_isCompact _ _ (fun _ => by positivity) E M
  let : CompactSpace S := isCompact_iff_compactSpace.mp hc
  have hf : Continuous (stateOfMomentSet : S → State n) :=
    continuous_induced_rng.mpr continuous_subtype_val
  have hi : Set.range (stateOfMomentSet : S → State n) = boundedStates n E M := by
    ext ρ
    constructor
    · rintro ⟨T, rfl⟩
      exact stateOfMomentSet_mem T
    · intro hρ
      exact ⟨⟨ρ.op, op_mem_momentSet hρ⟩, State.ext_op rfl⟩
  rw [← hi]
  exact isCompact_range hf

theorem continuous_entropy_boundedStates (n : ℕ) (E M : ℝ) :
    Continuous (fun ρ : boundedStates n E M => entropy ρ.val) := by
  rw [continuous_iff_continuousAt]
  intro ρ
  exact tendsto_entropy (fun σ => σ.property.1) ρ.property.1
    (fun σ => σ.property.2.1) ρ.property.2.1
    ((continuous_state_op n).comp continuous_subtype_val).continuousAt

theorem penalty_lowerSemicontinuous (n : ℕ) (E M : ℝ) {b ζ : ℝ} (hb : 0 ≤ b) (hζ : 0 ≤ ζ) :
    LowerSemicontinuous (fun ρ : boundedStates n E M => b*energy ρ.val+ζ*numberMoment 4 ρ.val) := by
  have he (ρ : boundedStates n E M) : b*energy ρ.val+ζ*numberMoment 4 ρ.val =
      ∑' k, (b*(totalNumber k : ℝ)+ζ*(1+(totalNumber k : ℝ))^4)*(entry ρ.val.op k k).re := by
    rw [energy, numberMoment, ← tsum_mul_left, ← tsum_mul_left,
      ← (ρ.property.1.mul_left b).tsum_add (ρ.property.2.2.1.mul_left ζ)]
    congr 1
    funext k
    ring
  simp only [he]
  apply lowerSemicontinuous_tsum_nonneg
  · intro ρ k
    apply mul_nonneg _ (ρ.val.positive.re_inner_nonneg_right _)
    positivity
  · intro ρ
    convert! (ρ.property.1.mul_left b).add (ρ.property.2.2.1.mul_left ζ) using 1
    funext k
    ring
  · intro k
    exact continuous_const.mul (Complex.continuous_re.comp (continuous_const.inner
      (((continuous_state_op n).comp continuous_subtype_val).clm_apply continuous_const)))

namespace Regularization
variable {n : ℕ} (R : Regularization n)

theorem continuous_output_entropy (E M : ℝ) :
    Continuous (fun p : boundedStates n E M × boundedStates n E M =>
      entropy (R.output p.1.val p.2.val)) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply tendsto_entropy (E := E+E+energy R.τD+energy R.τ0)
    (fun q => regularizedOutput_finiteEnergy _ _ _ _ _ _ R.finiteD R.finite0
      q.1.property.1 q.2.property.1)
    (regularizedOutput_finiteEnergy _ _ _ _ _ _ R.finiteD R.finite0 p.1.property.1 p.2.property.1)
  · intro q
    exact (regularizedOutput_energy_bound _ _ _ _ _ _ R.finiteD R.finite0
      q.1.property.1 q.2.property.1).trans (by linarith [q.1.property.2.1, q.2.property.2.1])
  · exact (regularizedOutput_energy_bound _ _ _ _ _ _ R.finiteD R.finite0
      p.1.property.1 p.2.property.1).trans (by linarith [p.1.property.2.1, p.2.property.2.1])
  · exact tendsto_regularizedOutput _ _ _ _ _ _ _ _
      ((continuous_state_op n).comp (continuous_subtype_val.comp continuous_fst)).continuousAt
      ((continuous_state_op n).comp (continuous_subtype_val.comp continuous_snd)).continuousAt

theorem objective_lowerSemicontinuous (E M : ℝ) :
    LowerSemicontinuous (fun p : boundedStates n E M × boundedStates n E M =>
      R.objective p.1.val p.2.val) := by
  have hc : Continuous (fun p : boundedStates n E M × boundedStates n E M =>
      R.c*entropy (R.output p.1.val p.2.val)-R.a1*entropy p.1.val-R.a2*entropy p.2.val) :=
    ((continuous_const.mul (R.continuous_output_entropy E M)).sub
      (continuous_const.mul ((continuous_entropy_boundedStates n E M).comp continuous_fst))).sub
      (continuous_const.mul ((continuous_entropy_boundedStates n E M).comp continuous_snd))
  exact (hc.lowerSemicontinuous.add
    ((penalty_lowerSemicontinuous n E M R.hb1.le R.hζ.le).comp continuous_fst)).add
    ((penalty_lowerSemicontinuous n E M R.hb2.le R.hζ.le).comp continuous_snd)

theorem sublevel_mem_bounded (C : ℝ) (ρ σ : State n)
    (h1 : FiniteMoment 4 ρ) (h2 : FiniteMoment 4 σ) (h : R.objective ρ σ ≤ C) :
    ρ ∈ boundedStates n (2*(C+R.entropyConstant)/R.b1+2*(C+R.entropyConstant)/R.b2)
      ((C+R.entropyConstant)/R.ζ) ∧
    σ ∈ boundedStates n (2*(C+R.entropyConstant)/R.b1+2*(C+R.entropyConstant)/R.b2)
      ((C+R.entropyConstant)/R.ζ) := by
  have hE1 := finiteMoment_finiteEnergy (by decide : 1 ≤ 4) h1
  have hE2 := finiteMoment_finiteEnergy (by decide : 1 ≤ 4) h2
  have hb := R.sublevel_bounds C ρ σ hE1 hE2 h
  have hp : 0 ≤ 2*(C+R.entropyConstant)/R.b1 := div_nonneg (by linarith [hb.1]) R.hb1.le
  have hq : 0 ≤ 2*(C+R.entropyConstant)/R.b2 := div_nonneg (by linarith [hb.1]) R.hb2.le
  exact ⟨⟨hE1, by linarith [hb.2.1], h1, hb.2.2.2.1⟩,
    ⟨hE2, by linarith [hb.2.2.1], h2, hb.2.2.2.2⟩⟩

theorem exists_constrained_minimum (E M : ℝ) (pw : boundedStates n E M × boundedStates n E M) :
    ∃ p : boundedStates n E M × boundedStates n E M,
      ∀ q : boundedStates n E M × boundedStates n E M,
        R.objective p.1.val p.2.val ≤ R.objective q.1.val q.2.val := by
  let : CompactSpace (boundedStates n E M) :=
    isCompact_iff_compactSpace.mp (boundedStates_isCompact n E M)
  obtain ⟨p, _, hp⟩ := LowerSemicontinuousOn.exists_isMinOn
    (s := Set.univ) ⟨pw, Set.mem_univ _⟩ isCompact_univ
    ((R.objective_lowerSemicontinuous E M).lowerSemicontinuousOn Set.univ)
  exact ⟨p, fun q => hp (Set.mem_univ q)⟩

theorem exists_minimum (ρw σw : State n) (hw1 : FiniteMoment 4 ρw) (hw2 : FiniteMoment 4 σw) :
    ∃ ρ σ : State n, FiniteMoment 4 ρ ∧ FiniteMoment 4 σ ∧
      R.objective ρ σ ≤ R.objective ρw σw ∧
      ∀ ρ' σ' : State n, FiniteMoment 4 ρ' → FiniteMoment 4 σ' →
        R.objective ρ σ ≤ R.objective ρ' σ' := by
  let C := R.objective ρw σw
  let E := 2*(C+R.entropyConstant)/R.b1+2*(C+R.entropyConstant)/R.b2
  let M := (C+R.entropyConstant)/R.ζ
  have hwm := R.sublevel_mem_bounded C ρw σw hw1 hw2 le_rfl
  let pw : boundedStates n E M × boundedStates n E M := (⟨ρw, hwm.1⟩, ⟨σw, hwm.2⟩)
  obtain ⟨p, hp⟩ := R.exists_constrained_minimum E M pw
  have hpw : R.objective p.1.val p.2.val ≤ C := hp pw
  refine ⟨p.1.val, p.2.val, p.1.property.2.2.1, p.2.property.2.2.1, hpw, ?_⟩
  intro ρ σ h1 h2
  by_cases h : R.objective ρ σ ≤ C
  · have hh := R.sublevel_mem_bounded C ρ σ h1 h2 h
    exact hp (⟨ρ, hh.1⟩, ⟨σ, hh.2⟩)
  · exact hpw.trans (le_of_lt (lt_of_not_ge h))

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
open QuantumTrace Filter Topology


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.Regularization.exists_minimum := @_root_.OAI.EntropyPhotonNumber.Regularization.exists_minimum
