-- Prove2me | solution 1 for OAI.QuantumTrace.entropy_le_thermal_crossEntropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:17:09.696977+00:00
-- url     : https://prove2.me/submissions/0b565a69-e90c-4fd7-9fb1-a27e5db88952

-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean:L613-L631
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.entropy_le_thermal_crossEntropy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Theorems.Thm_OAI_QuantumTrace_cfc_apply_eigenvector
import Theorems.Thm_OAI_QuantumTrace_entropy_summable_and_le_crossEntropy
import Theorems.Thm_OAI_QuantumTrace_exists_positive_eigenbasis

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

theorem tsum_thermal_crossEntropy {n : ℕ} {p : (Fin n → ℕ) → ℝ}
    (hp : HasSum p 1) (hE : Summable (fun k => (∑ j, (k j : ℝ)) * p k))
    {r : ℝ} (hr : 0 < r) :
    (∑' k, p k * (-Real.log (thermalWeight n r k))) =
      n * Real.log (r + 1) + (∑' k, (∑ j, (k j : ℝ)) * p k) * Real.log ((r + 1) / r) := by
  have he (k : Fin n → ℕ) : p k * (-Real.log (thermalWeight n r k)) =
      p k * (n * Real.log (r + 1)) + ((∑ j, (k j : ℝ)) * p k) * Real.log ((r + 1) / r) := by
    rw [log_thermalWeight n hr k]; ring
  simp only [he]
  rw [(hp.summable.mul_right _).tsum_add (hE.mul_right _), tsum_mul_right,
    tsum_mul_right, hp.tsum_eq, one_mul]

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

theorem entropy_le_thermal_crossEntropy {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive)
    (ht : HasSum (fun k => (inner ℂ (b k) (T (b k))).re) 1)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re))
    {r : ℝ} (hr : 0 < r) :
    (∑' k, (inner ℂ (b k) (entropyOperator T (b k))).re) ≤
      n * Real.log (r + 1) +
      (∑' k, (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re) * Real.log ((r + 1) / r) := by
  have hc := entropy_summable_and_le_crossEntropy
    (fun k => (inner ℂ (b k) (T (b k))).re) (thermalWeight n r)
    (fun k => hp.re_inner_nonneg_right (b k)) (thermalWeight_pos n hr)
    ht (hasSum_thermalWeight n hr) (summable_thermal_crossEntropy ht.summable hE hr)
  calc
    _ ≤ ∑' k, Real.negMulLog (inner ℂ (b k) (T (b k))).re :=
      (entropy_summable_finite_energy b hp ht hE).tsum_le_tsum
        (fun k => entropyOperator_quadratic_le b hp ht (b k) (b.orthonormal.norm_eq_one k)) hc.1
    _ ≤ _ := by
      rw [← tsum_thermal_crossEntropy ht hE hr]
      exact hc.2

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

-- ---- platform node ----
open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory


theorem solution : type_of% @_root_.OAI.QuantumTrace.entropy_le_thermal_crossEntropy := @_root_.OAI.QuantumTrace.entropy_le_thermal_crossEntropy
