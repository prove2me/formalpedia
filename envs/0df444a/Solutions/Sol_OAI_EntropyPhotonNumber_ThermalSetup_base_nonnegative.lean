-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.ThermalSetup.base_nonnegative
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:59:06.604008+00:00
-- url     : https://prove2.me/submissions/a4e2ad81-71ed-4a9a-b6b5-d893e4c560c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/ThermalLimit.lean:L682-L726
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.ThermalSetup.base_nonnegative. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalLimit
import Theorems.Thm_OAI_BeamLadder_adjoint_covariance
import Theorems.Thm_OAI_BeamLadder_discarded_covariance
import Theorems.Thm_OAI_BeamLadder_output_weak
import Theorems.Thm_OAI_BeamLadder_radial_covariance
import Theorems.Thm_OAI_BeamLadder_retained_covariance
import Theorems.Thm_OAI_BeamLadder_tensorPreimage_lowerL
import Theorems.Thm_OAI_BeamLadder_tensorPreimage_lowerR
import Theorems.Thm_OAI_BeamLadder_tensorPreimage_raiseL
import Theorems.Thm_OAI_BeamLadder_tensorPreimage_raiseR
import Theorems.Thm_OAI_CrossEnsemble_operator_comp_left
import Theorems.Thm_OAI_EntropyPhotonNumber_Regularization_exists_minimum
import Theorems.Thm_OAI_EntropyPhotonNumber_Regularization_sublevel_bounds
import Theorems.Thm_OAI_EntropyPhotonNumber_ThermalSetup_minimum_decay
import Theorems.Thm_OAI_EntropyPhotonNumber_WeightedColumns_lowerEnergy_hasSum
import Theorems.Thm_OAI_EntropyPhotonNumber_WeightedColumns_thermal_lowerEnergy
import Theorems.Thm_OAI_EntropyPhotonNumber_beamOutput_powerMoment_le
import Theorems.Thm_OAI_EntropyPhotonNumber_regularizedOutput_energy_bound
import Theorems.Thm_OAI_EntropyPhotonNumber_thermalGenerator_drift
import Theorems.Thm_OAI_PhysicalGenerator_weakOperator_entry
import Theorems.Thm_OAI_QuantumTrace_cfc_apply_eigenvector
import Theorems.Thm_OAI_QuantumTrace_energySet_limit
import Theorems.Thm_OAI_QuantumTrace_energySet_totallyBounded
import Theorems.Thm_OAI_QuantumTrace_entropy_le_thermal_crossEntropy
import Theorems.Thm_OAI_QuantumTrace_entropy_small_mass_bound
import Theorems.Thm_OAI_QuantumTrace_entropy_summable_and_le_crossEntropy
import Theorems.Thm_OAI_QuantumTrace_exists_positive_eigenbasis
import Theorems.Thm_OAI_QuantumTrace_tendsto_tsum_of_uniform_tail
import Theorems.Thm_OAI_ThermalMetric_defectVector_mem_centeredSpace
import Theorems.Thm_OAI_ThermalRecurrence_unique_thermal_matrix
import Theorems.Thm_OAI_WeightedGenerator_negative_quartic_bounded
import Theorems.Thm_OAI_WeightedGenerator_weakDefect_numberMatrixUnit
import Theorems.Thm_OAI_WeightedGenerator_weakDefect_spectral

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

-- ---- from OAI.MathematicalPhysics.Fock.Operators ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate

namespace WeightedShift
variable {I J : Type*}
variable [DecidableEq I] [DecidableEq J]

end WeightedShift

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace CrossEnsemble
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem trace_norm_summable (b : HilbertBasis J ℂ E) {u v : I → E}
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2)) :
    Summable (fun ij : I × J => ‖inner ℂ (b ij.2) (u ij.1)*inner ℂ (v ij.1) (b ij.2)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((square_coordinates_summable b hu).add (square_coordinates_summable b hv))
  intro ij
  rw [norm_mul, norm_inner_symm (v ij.1)]
  nlinarith [sq_nonneg (‖inner ℂ (b ij.2) (u ij.1)‖-‖inner ℂ (b ij.2) (v ij.1)‖)]

theorem trace_hasSum (b : HilbertBasis J ℂ E) {u v : I → E}
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2)) :
    HasSum (fun j => inner ℂ (b j) (operator u v (b j)))
      (∑' i, inner ℂ (v i) (u i)) := by
  have hh := (trace_norm_summable b hu hv).of_norm
  have hi (i : I) : HasSum (fun j => inner ℂ (b j) (u i)*inner ℂ (v i) (b j)) (inner ℂ (v i) (u i)) := by
    simpa only [mul_comm] using b.hasSum_inner_mul_inner (v i) (u i)
  have he (j : J) := entry_hasSum hu hv (b j) (b j)
  have hf := hh.hasSum.prod_fiberwise (f := fun ij : I × J => inner ℂ (b ij.2) (u ij.1)*inner ℂ (v ij.1) (b ij.2)) hi
  have hg := hh.prod_symm.hasSum.prod_fiberwise (f := fun ji : J × I => inner ℂ (b ji.1) (u ji.2)*inner ℂ (v ji.2) (b ji.1)) he
  have ht : (∑' j, inner ℂ (b j) (operator u v (b j)))=∑' i, inner ℂ (v i) (u i) := by
    rw [hg.tsum_eq, hf.tsum_eq]
    exact (Equiv.prodComm J I).tsum_eq (fun ij : I × J => inner ℂ (b ij.2) (u ij.1)*inner ℂ (v ij.1) (b ij.2))
  exact ht ▸ hg.summable.hasSum

theorem pairing_trace (b : HilbertBasis J ℂ E) {u v : I → E}
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    HasSum (fun j => inner ℂ (b j) (Z (operator u v (b j)))) (pairing u v Z) := by
  have hh := trace_hasSum b (applied_summable hu Z) hv
  rw [← operator_comp_left hu hv Z] at hh
  exact hh

end CrossEnsemble

namespace CrossEnsemble
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped BigOperators ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end WeightedGenerator

end

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.BeamTrace ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
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
theorem weight_down (j : Fin n) (k : NumberIndex n) (hk : 0 < k j) :
    numberWeight (down j k)=numberWeight k-1 := by
  have hh := weight_up j (down j k)
  rw [up_down j k hk] at hh
  linarith
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

theorem retained_adjoint_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    (lowerL j).adjoint ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        ((Real.sqrt η:ℂ) • (lowerL j).adjoint+(Real.sqrt (1-η):ℂ) • (lowerR j).adjoint) := by
  simpa only [map_add, map_smulₛₗ, Complex.conj_ofReal] using
    adjoint_covariance (beamUnitary η hη) (lowerL j) _ (retained_covariance η hη j)

theorem discarded_adjoint_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    (lowerR j).adjoint ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (-(Real.sqrt (1-η):ℂ) • (lowerL j).adjoint+(Real.sqrt η:ℂ) • (lowerR j).adjoint) := by
  simpa only [map_add, map_smulₛₗ, map_neg, Complex.conj_ofReal] using
    adjoint_covariance (beamUnitary η hη) (lowerR j) _ (discarded_covariance η hη j)
end

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

theorem retained_creation_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    raiseL j ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        ((Real.sqrt η:ℂ) • raiseL j+(Real.sqrt (1-η):ℂ) • raiseR j) := by
  unfold raiseL raiseR
  rw [ContinuousLinearMap.comp_assoc, retained_adjoint_covariance,
    ← ContinuousLinearMap.comp_assoc, radial_covariance, ContinuousLinearMap.comp_assoc]
  congr 1
  ext x ke
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, map_add, map_smul]

theorem discarded_creation_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    raiseR j ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (-(Real.sqrt (1-η):ℂ) • raiseL j+(Real.sqrt η:ℂ) • raiseR j) := by
  unfold raiseL raiseR
  rw [ContinuousLinearMap.comp_assoc, discarded_adjoint_covariance,
    ← ContinuousLinearMap.comp_assoc, radial_covariance, ContinuousLinearMap.comp_assoc]
  congr 1
  ext x ke
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, map_add, map_smul]

theorem raiseR_up (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    raiseR j x (upR j ke)=((Real.sqrt ((ke.2 j:ℝ)+1)/W ke:ℝ):ℂ)*x ke := by
  change (increase (W (upR j ke)):ℂ)*((lowerR j).adjoint x (upR j ke))=_
  rw [lowerR, WeightedShift.adjoint_apply_image]
  have hw : 0<W ke := by linarith [W_one_le ke]
  simp only [W_upR, increase, ite_eq_left (by linarith : 1<W ke+1), add_sub_cancel_right,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, map_div₀, map_add, map_one, Complex.conj_ofReal]
  have hw1 : (W ke:ℂ)+1≠0 := by exact_mod_cast (by linarith : W ke+1≠0)
  field_simp

theorem raiseR_zero (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n)
    (hk : ke.2 j=0) : raiseR j x ke=0 := by
  change _*((lowerR j).adjoint x ke)=0
  rw [lowerR, WeightedShift.adjoint_apply_outside]
  · exact mul_zero _
  · intro ab he
    have hh := congrArg (fun q => q.2 j) he
    simp only [upR, up_same, hk] at hh
    omega
end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

theorem inverse_selfAdjoint : IsSelfAdjoint (inverse (n:=n)) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  apply HasSum.unique (lp.hasSum_inner (𝕜:=ℂ) (inverse x) y)
  convert! lp.hasSum_inner (𝕜:=ℂ) x (inverse y) using 1
  ext ke
  simp only [inverse_apply, RCLike.inner_apply, map_mul, map_inv₀, Complex.conj_ofReal]
  ring

theorem inverse_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) :
    inverse ∘L (beamUnitary (n:=n) η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L inverse :=
  radial_covariance η hη (fun t => t⁻¹) 1 (by norm_num) inverse_bound

theorem slice_raiseR_up (j : Fin n) (x : JointFock n) (e : NumberIndex n) :
    slice (raiseR j x) (up j e)=(Real.sqrt ((e j:ℝ)+1):ℂ) • slice (inverse x) e := by
  apply lp.ext
  funext k
  change raiseR j x (upR j (k,e))=_
  rw [raiseR_up]
  simp only [slice_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, inverse_apply,
    div_eq_mul_inv]
  push_cast
  ring

theorem slice_raiseR_zero (j : Fin n) (x : JointFock n) (e : NumberIndex n)
    (he : e j=0) : slice (raiseR j x) e=0 := by
  apply lp.ext
  funext k
  exact raiseR_zero j x (k,e) he

theorem discarded_commutator_operator (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    inverse ∘L liftLeft Z ∘L raiseR j =
      (lowerR j).adjoint ∘L liftLeft Z ∘L inverse := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  by_cases he : 0<e j
  · obtain ⟨f,hf⟩ : ∃ f, e=up j f := ⟨down j e,(up_down j e he).symm⟩
    subst e
    change inverse (liftLeft Z (raiseR j x)) (k,up j f)=
      (lowerR j).adjoint (liftLeft Z (inverse x)) (upR j (k,f))
    rw [inverse_apply, liftLeft_apply]
    rw [slice_raiseR_up, map_smul]
    rw [lowerR, WeightedShift.adjoint_apply_image]
    simp only [show W (k,up j f)=W (k,f)+1 from W_upR j (k,f),
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, liftLeft_apply, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_div, map_div₀, map_add, map_one, Complex.conj_ofReal]
    ring
  · have hz : e j=0 := Nat.eq_zero_of_not_pos he
    change _*Z (slice (raiseR j x) e) k=(lowerR j).adjoint (liftLeft Z (inverse x)) (k,e)
    rw [slice_raiseR_zero j x e hz, map_zero]
    rw [lowerR, WeightedShift.adjoint_apply_outside]
    · exact mul_zero _
    · intro ab hh
      have h := congrArg (fun q => q.2 j) hh
      simp only [upR, up_same, hz] at h
      omega

theorem discarded_commutator (j : Fin n) (Z : Fock n →L[ℂ] Fock n)
    (x y : JointFock n) :
    inner ℂ (inverse x) (liftLeft Z (raiseR j y))=
      inner ℂ (lowerR j x) (liftLeft Z (inverse y)) := by
  have hi : inner ℂ (inverse x) (liftLeft Z (raiseR j y))=
      inner ℂ x (inverse (liftLeft Z (raiseR j y))) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (inverse_selfAdjoint (n:=n))) x _
  rw [hi]
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T y)
    (discarded_commutator_operator j Z)
  change inverse (liftLeft Z (raiseR j y))=(lowerR j).adjoint (liftLeft Z (inverse y)) at hh
  rw [hh, ContinuousLinearMap.adjoint_inner_right]

theorem conjugate_inner (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n)
    (x y : JointFock n) :
    inner ℂ x (conjugate η hη Z y)=inner ℂ (beamUnitary η hη x) (liftLeft Z (beamUnitary η hη y)) := by
  change inner ℂ x ((beamUnitary η hη).symm (liftLeft Z (beamUnitary η hη y)))=_
  rw [← (beamUnitary η hη).inner_map_map, (beamUnitary η hη).apply_symm_apply]

theorem covariance_lower_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    lowerL j (beamUnitary η hη x)=(Real.sqrt η:ℂ) • beamUnitary η hη (lowerL j x)+
      (Real.sqrt (1-η):ℂ) • beamUnitary η hη (lowerR j x) := by
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (retained_covariance η hη j)
  change lowerL j (beamUnitary η hη x)=beamUnitary η hη ((Real.sqrt η:ℂ) • lowerL j x+(Real.sqrt (1-η):ℂ) • lowerR j x) at hh
  simpa only [map_add, map_smul] using hh

theorem covariance_raise_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    raiseL j (beamUnitary η hη x)=(Real.sqrt η:ℂ) • beamUnitary η hη (raiseL j x)+
      (Real.sqrt (1-η):ℂ) • beamUnitary η hη (raiseR j x) := by
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (retained_creation_covariance η hη j)
  change raiseL j (beamUnitary η hη x)=beamUnitary η hη ((Real.sqrt η:ℂ) • raiseL j x+(Real.sqrt (1-η):ℂ) • raiseR j x) at hh
  simpa only [map_add, map_smul] using hh

theorem covariance_inverse_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x : JointFock n) :
    inverse (beamUnitary η hη x)=beamUnitary η hη (inverse x) :=
  congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (inverse_covariance η hη)

theorem covariance_discarded_lower_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    lowerR j (beamUnitary η hη x)=-(Real.sqrt (1-η):ℂ) • beamUnitary η hη (lowerL j x)+
      (Real.sqrt η:ℂ) • beamUnitary η hη (lowerR j x) := by
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (discarded_covariance η hη j)
  change lowerR j (beamUnitary η hη x)=beamUnitary η hη (-(Real.sqrt (1-η):ℂ) • lowerL j x+(Real.sqrt η:ℂ) • lowerR j x) at hh
  simpa only [map_add, map_smul] using hh

theorem covariance_discarded_raise_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    raiseR j (beamUnitary η hη x)=-(Real.sqrt (1-η):ℂ) • beamUnitary η hη (raiseL j x)+
      (Real.sqrt η:ℂ) • beamUnitary η hη (raiseR j x) := by
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (discarded_creation_covariance η hη j)
  change raiseR j (beamUnitary η hη x)=beamUnitary η hη (-(Real.sqrt (1-η):ℂ) • raiseL j x+(Real.sqrt η:ℂ) • raiseR j x) at hh
  simpa only [map_add, map_smul] using hh

theorem two_port_algebra (c s r a b A B C D : ℂ) (hs : c^2+s^2=1)
    (hr : r=c^2*a+s^2*b) (hd : -s*A+c*B= -s*C+c*D) :
    (r+1)*(c*A+s*B)-r*(c*C+s*D)=
      c*((a+1)*A-a*C)+s*((b+1)*B-b*D) := by
  rw [hr]
  linear_combination (c*a*(A-C)+s*b*(B-D))*hs+c*s*(a-b)*hd

theorem physical_weak_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (a b : ℝ) (j : Fin n)
    (x y : JointFock n) (Z : Fock n →L[ℂ] Fock n) :
    weakL (η*a+(1-η)*b) j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z)=
      (Real.sqrt η:ℂ)*weakL a j x y (conjugate η hη Z)+
        (Real.sqrt (1-η):ℂ)*weakR b j x y (conjugate η hη Z) := by
  have hd := discarded_commutator j Z (beamUnitary η hη x) (beamUnitary η hη y)
  rw [covariance_inverse_apply, covariance_inverse_apply, covariance_discarded_lower_apply,
    covariance_discarded_raise_apply] at hd
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, map_neg, Complex.conj_ofReal, ← conjugate_inner] at hd
  unfold weakL weakR
  rw [covariance_lower_apply, covariance_raise_apply, covariance_inverse_apply, covariance_inverse_apply]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, ← conjugate_inner]
  apply two_port_algebra
  · have hc : (Real.sqrt η:ℂ)^2=(η:ℂ) := by exact_mod_cast Real.sq_sqrt hη.1
    have hs : (Real.sqrt (1-η):ℂ)^2=(1-η:ℂ) := by exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hη.2)
    rw [hc, hs]
    ring
  · norm_cast
    rw [Real.sq_sqrt hη.1, Real.sq_sqrt (sub_nonneg.mpr hη.2)]
  · exact hd.symm
end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

theorem tensorPreimage_apply (x y : Fock n) (k e : NumberIndex n) :
    tensorPreimage x y (k,e)=(W (k,e):ℂ)*inverseWeight 3 x k*inverseWeight 3 y e := by
  have hk : (numberWeight k:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le k] : numberWeight k≠0)
  have he : (numberWeight e:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le e] : numberWeight e≠0)
  simp only [tensorPreimage, lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply,
    tensor_apply, inverseWeight_apply, W]
  push_cast
  field_simp

theorem tensorPreimage_inverse (x y : Fock n) :
    inverse (tensorPreimage x y)=tensor (inverseWeight 3 x) (inverseWeight 3 y) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  rw [inverse_apply, tensorPreimage_apply, tensor_apply]
  have hw : (W (k,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (k,e)] : W (k,e)≠0)
  field_simp

theorem square_add_summable {I E : Type*} [NormedAddCommGroup E] {x y : I → E}
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2)) :
    Summable (fun i => ‖x i+y i‖^2) := by
  have hmx : Memℓp x 2 := by
    simpa only [memℓp_gen_iff (by norm_num : (0:ℝ)<(2:ENNReal).toReal), ENNReal.toReal_ofNat, Real.rpow_two] using hx
  have hmy : Memℓp y 2 := by
    simpa only [memℓp_gen_iff (by norm_num : (0:ℝ)<(2:ENNReal).toReal), ENNReal.toReal_ofNat, Real.rpow_two] using hy
  simpa only [memℓp_gen_iff (by norm_num : (0:ℝ)<(2:ENNReal).toReal), ENNReal.toReal_ofNat, Real.rpow_two, Pi.add_apply] using hmx.add hmy

theorem tensorPreimage_summable {I J : Type*} (x : I → Fock n) (y : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2)) :
    Summable (fun ij : I × J => ‖tensorPreimage (x ij.1) (y ij.2)‖^2) := by
  have ht (a b : ℕ) : Summable (fun ij : I × J => ‖tensor (inverseWeight a (x ij.1)) (inverseWeight b (y ij.2))‖^2) := by
    simpa only [tensor_norm_sq] using
      (CrossEnsemble.applied_summable hx (inverseWeight a)).mul_of_nonneg
        (CrossEnsemble.applied_summable hy (inverseWeight b)) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  have hn : Summable (fun ij : I × J => ‖-tensor (inverseWeight 3 (x ij.1)) (inverseWeight 3 (y ij.2))‖^2) := by
    simpa only [norm_neg] using ht 3 3
  simpa only [tensorPreimage, sub_eq_add_neg] using square_add_summable (square_add_summable (ht 2 3) (ht 3 2)) hn
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

 theorem conditionalLeft_entry (y : J → H B) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) (u v : H A) :
    HasSum (fun j => inner ℂ (tensor u (y j)) (Z (tensor v (y j)))) (inner ℂ u (conditionalLeft y hy Z v)) :=
  KrausBounded.dual_entry _ _ _ _ _

 theorem conditionalRight_entry (x : I → H A) (hx : HasSum (fun i => ‖x i‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) (u v : H B) :
    HasSum (fun i => inner ℂ (tensor (x i) u) (Z (tensor (x i) v))) (inner ℂ u (conditionalRight x hx Z v)) :=
  KrausBounded.dual_entry _ _ _ _ _

 theorem tensorFamily_summable (x : I → H A) (y : J → H B)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2)) :
    Summable (fun ij : I × J => ‖tensor (x ij.1) (y ij.2)‖^2) := by
  simpa only [tensor_norm_sq] using hx.mul_of_nonneg hy (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)

theorem pairing_conditionalLeft (u v : I → H A) (y : J → H B)
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2))
    (hy : HasSum (fun j => ‖y j‖^2) 1) (Z : H (A × B) →L[ℂ] H (A × B)) :
    CrossEnsemble.pairing (fun ij : I × J => tensor (u ij.1) (y ij.2))
      (fun ij : I × J => tensor (v ij.1) (y ij.2)) Z=
      CrossEnsemble.pairing u v (conditionalLeft y hy Z) := by
  have hh := (CrossEnsemble.pairing_summable (tensorFamily_summable u y hu hy.summable)
    (tensorFamily_summable v y hv hy.summable) Z).hasSum.prod_fiberwise
      (fun i => conditionalLeft_entry y hy Z (v i) (u i))
  exact hh.tsum_eq.symm

theorem pairing_conditionalRight (x : I → H A) (u v : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1)
    (hu : Summable (fun j => ‖u j‖^2)) (hv : Summable (fun j => ‖v j‖^2))
    (Z : H (A × B) →L[ℂ] H (A × B)) :
    CrossEnsemble.pairing (fun ij : I × J => tensor (x ij.1) (u ij.2))
      (fun ij : I × J => tensor (x ij.1) (v ij.2)) Z=
      CrossEnsemble.pairing u v (conditionalRight x hx Z) := by
  have hs := CrossEnsemble.pairing_summable (tensorFamily_summable x u hx.summable hu)
    (tensorFamily_summable x v hx.summable hv) Z
  have hh := hs.prod_symm.hasSum.prod_fiberwise
      (fun j => conditionalRight_entry x hx Z (v j) (u j))
  have he := (Equiv.prodComm J I).tsum_eq
    (fun ij : I × J => inner ℂ (tensor (x ij.1) (v ij.2)) (Z (tensor (x ij.1) (u ij.2))))
  change (∑' ji : J × I, inner ℂ (tensor (x ji.swap.1) (v ji.swap.2))
    (Z (tensor (x ji.swap.1) (u ji.swap.2))))=_ at he
  rw [he] at hh
  exact hh.tsum_eq.symm
end TensorLp

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

theorem weakL_summable (r : ℝ) (j : Fin n) (x y : I → JointFock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (T : JointFock n →L[ℂ] JointFock n) :
    Summable (fun i => weakL r j (x i) (y i) T) :=
  ((CrossEnsemble.pairing_summable (CrossEnsemble.applied_summable hy inverse)
    (CrossEnsemble.applied_summable hx (lowerL j)) T).mul_left _).sub
  ((CrossEnsemble.pairing_summable (CrossEnsemble.applied_summable hy (raiseL j))
    (CrossEnsemble.applied_summable hx inverse) T).mul_left _)

theorem weakR_summable (r : ℝ) (j : Fin n) (x y : I → JointFock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (T : JointFock n →L[ℂ] JointFock n) :
    Summable (fun i => weakR r j (x i) (y i) T) :=
  ((CrossEnsemble.pairing_summable (CrossEnsemble.applied_summable hy inverse)
    (CrossEnsemble.applied_summable hx (lowerR j)) T).mul_left _).sub
  ((CrossEnsemble.pairing_summable (CrossEnsemble.applied_summable hy (raiseR j))
    (CrossEnsemble.applied_summable hx inverse) T).mul_left _)

theorem weakL_product (r : ℝ) (j : Fin n) (x : I → Fock n) (y : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2))
    (hy : HasSum (fun j => ‖inverseWeight 3 (y j)‖^2) 1)
    (Z : JointFock n →L[ℂ] JointFock n) :
    (∑' ij : I × J, weakL r j (tensorPreimage (x ij.1) (y ij.2))
      (tensorPreimage (x ij.1) (y ij.2)) Z)=
        singleWeak r j x (conditionalLeft (fun j => inverseWeight 3 (y j)) hy Z) := by
  have hi := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hl := CrossEnsemble.applied_summable hx (sandwich 0 3 (by omega) j)
  have hr := CrossEnsemble.applied_summable hx (creationSandwich 0 3 (by omega) j)
  simp only [weakL, tensorPreimage_lowerL, tensorPreimage_inverse, tensorPreimage_raiseL]
  rw [Summable.tsum_sub (((CrossEnsemble.pairing_summable (tensorFamily_summable _ _ hi hy.summable)
    (tensorFamily_summable _ _ hl hy.summable) Z).mul_left _))
    (((CrossEnsemble.pairing_summable (tensorFamily_summable _ _ hr hy.summable)
    (tensorFamily_summable _ _ hi hy.summable) Z).mul_left _)), tsum_mul_left, tsum_mul_left]
  change (r+1:ℂ)*CrossEnsemble.pairing _ _ Z-(r:ℂ)*CrossEnsemble.pairing _ _ Z=_
  rw [pairing_conditionalLeft _ _ _ hi hl hy, pairing_conditionalLeft _ _ _ hr hi hy]
  rfl

theorem weakR_product (r : ℝ) (j : Fin n) (x : I → Fock n) (y : J → Fock n)
    (hx : HasSum (fun i => ‖inverseWeight 3 (x i)‖^2) 1)
    (hy : Summable (fun j => ‖y j‖^2))
    (Z : JointFock n →L[ℂ] JointFock n) :
    (∑' ij : I × J, weakR r j (tensorPreimage (x ij.1) (y ij.2))
      (tensorPreimage (x ij.1) (y ij.2)) Z)=
        singleWeak r j y (conditionalRight (fun i => inverseWeight 3 (x i)) hx Z) := by
  have hi := CrossEnsemble.applied_summable hy (inverseWeight 3)
  have hl := CrossEnsemble.applied_summable hy (sandwich 0 3 (by omega) j)
  have hr := CrossEnsemble.applied_summable hy (creationSandwich 0 3 (by omega) j)
  simp only [weakR, tensorPreimage_lowerR, tensorPreimage_inverse, tensorPreimage_raiseR]
  rw [Summable.tsum_sub (((CrossEnsemble.pairing_summable (tensorFamily_summable _ _ hx.summable hi)
    (tensorFamily_summable _ _ hx.summable hl) Z).mul_left _))
    (((CrossEnsemble.pairing_summable (tensorFamily_summable _ _ hx.summable hr)
    (tensorFamily_summable _ _ hx.summable hi) Z).mul_left _)), tsum_mul_left, tsum_mul_left]
  change (r+1:ℂ)*CrossEnsemble.pairing _ _ Z-(r:ℂ)*CrossEnsemble.pairing _ _ Z=_
  rw [pairing_conditionalRight _ _ _ hx hi hl, pairing_conditionalRight _ _ _ hx hr hi]
  rfl

theorem product_weak_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (a b : ℝ) (j : Fin n)
    (x : I → Fock n) (y : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hxn : HasSum (fun i => ‖inverseWeight 3 (x i)‖^2) 1)
    (hyn : HasSum (fun j => ‖inverseWeight 3 (y j)‖^2) 1)
    (Z : Fock n →L[ℂ] Fock n) :
    (∑' ij : I × J, weakL (η*a+(1-η)*b) j
      (beamUnitary η hη (tensorPreimage (x ij.1) (y ij.2)))
      (beamUnitary η hη (tensorPreimage (x ij.1) (y ij.2))) (liftLeft Z))=
    (Real.sqrt η:ℂ)*singleWeak a j x (conditionalLeft (fun j => inverseWeight 3 (y j)) hyn (conjugate η hη Z))+
    (Real.sqrt (1-η):ℂ)*singleWeak b j y (conditionalRight (fun i => inverseWeight 3 (x i)) hxn (conjugate η hη Z)) := by
  have hs := tensorPreimage_summable x y hx hy
  simp only [physical_weak_covariance]
  rw [Summable.tsum_add ((weakL_summable a j _ _ hs hs _).mul_left _)
    ((weakR_summable b j _ _ hs hs _).mul_left _), tsum_mul_left, tsum_mul_left,
    weakL_product a j x y hx hyn, weakR_product b j x y hxn hy]
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

-- ---- from OAI.InformationTheory.PhotonNumber.ThermalMetric ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace ThermalMetric

section
open EntropyPhotonNumber DiagonalForms.System

end

section
open DiagonalForms.System

end

section
open EntropyPhotonNumber
variable {J : Type*}

theorem weightedVector_norm_sq (a : J → ℝ) (z : J → ℂ)
    (hz : Summable (fun j => a j*‖z j‖^2)) (ha : ∀ j, 0 ≤ a j) :
    ‖weightedVector a z hz ha‖^2=∑' j, a j*‖z j‖^2 := by
  have hh := lp.hasSum_norm (p := 2) (by norm_num : 0 < (2:ENNReal).toReal) (weightedVector a z hz ha)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, weightedVector_apply, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (ha _)] using hh.tsum_eq.symm

theorem defectVector_pairing (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ) (hd) (z : J × J → ℂ)
    (hz : Summable (fun a : J × J => metricCoefficient r (p a.1) (p a.2)*‖z a‖^2)) :
    HasSum (fun a : J × J => (defectCoefficient r (p a.1) (p a.2):ℂ)*conj (d a)*z a)
      (inner ℂ (defectVector r hr p hp d hd)
        (weightedVector (fun a => metricCoefficient r (p a.1) (p a.2)) z hz
          (fun a => (metricCoefficient_pos hr (hp a.1) (hp a.2)).le))) := by
  have hh := lp.hasSum_inner (𝕜 := ℂ) (defectVector r hr p hp d hd)
    (weightedVector (fun a => metricCoefficient r (p a.1) (p a.2)) z hz
      (fun a => (metricCoefficient_pos hr (hp a.1) (hp a.2)).le))
  convert! hh using 1
  ext a
  simp only [defectVector_apply, weightedVector_apply, RCLike.inner_apply,
    map_mul, Complex.ofReal_div, map_div₀, Complex.conj_ofReal]
  have hn : (Real.sqrt (metricCoefficient r (p a.1) (p a.2)):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (metricCoefficient_pos hr (hp a.1) (hp a.2))).ne'
  field_simp

end

section
variable {J : Type*}

theorem defectFunctional_restrict_norm (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ) (hd) (P : Submodule ℂ (lp (fun _ : J × J => ℂ) 2))
    (hv : defectVector r hr p hp d hd ∈ P) :
    ‖(defectFunctional r hr p hp d hd).comp P.subtypeL‖=
      ‖defectFunctional r hr p hp d hd‖ := by
  have he : (defectFunctional r hr p hp d hd).comp P.subtypeL =
      innerSL ℂ (⟨defectVector r hr p hp d hd,hv⟩ : P) := by
    ext z
    rfl
  rw [he, innerSL_apply_norm, defectFunctional, innerSL_apply_norm]
  rfl
end

open scoped ComplexConjugate
variable {J : Type*}

theorem diagonal_mean_summable (p : J → ℝ) (hp : ∀ j, 0≤p j) (hs : Summable p)
    (d : J × J → ℂ) (hd : Summable (fun a : J × J => p a.2*‖d a‖^2)) :
    Summable (fun j => (p j:ℂ)*d (j,j)) := by
  have hi : Function.Injective (fun j : J => (j,j)) := fun _ _ he => (Prod.mk.inj he).1
  have hh := hd.comp_injective hi
  apply Summable.of_norm_bounded (hh.add hs)
  intro j
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp j)]
  have hn : ‖d (j,j)‖≤‖d (j,j)‖^2+1 := by nlinarith [sq_nonneg (‖d (j,j)‖-1)]
  simpa only [mul_add, mul_one, Function.comp_apply] using mul_le_mul_of_nonneg_left hn (hp j)

theorem diagonal_centering (p : J → ℝ) (hs : HasSum p 1)
    (d : J × J → ℂ) (hd : Summable (fun j => (p j:ℂ)*d (j,j))) :
    HasSum (fun j => (p j:ℂ)*(d (j,j)-diagonalMean p d)) 0 := by
  have hh := hd.hasSum.sub ((Complex.hasSum_ofReal.mpr hs).mul_right (diagonalMean p d))
  simpa only [diagonalMean, Complex.ofReal_one, one_mul, sub_self, mul_sub] using hh

end ThermalMetric

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace Annihilation
open EntropyPhotonNumber
variable {n : ℕ} {J : Type*}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

theorem annihilation_mean_summable (j : Fin n) :
    Summable (fun r => (G.probability r:ℂ)*G.annihilationMatrix j (r,r)) := by
  apply diagonal_mean_summable G.probability (fun r => (G.probability_pos r).le)
    G.probability_sum.summable
  have hh := nonlog_summable G.basis G.spectralColumns G.spectralColumns_summable j false
  simpa only [spectralGain_lowering_sq G.basis G.probability G.probability_pos,
    annihilationMatrix] using hh

theorem centeredMatrix_mean_zero (j : Fin n) :
    HasSum (fun r => (G.probability r:ℂ)*G.centeredMatrix j (r,r)) 0 := by
  classical
  simpa only [centeredMatrix, centeredEntry, ↓reduceIte, annihilationMean, annihilationMatrix]
    using diagonal_centering G.probability G.probability_sum
      (G.annihilationMatrix j) (G.annihilation_mean_summable j)

end EntropyPhotonNumber.GibbsData

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace ThermalMetric
open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalMetric

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

namespace Annihilation
open EntropyPhotonNumber
variable {n : ℕ}

theorem lowering_weighted_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    lowering j (inverseWeight 2 x) k=
      (Real.sqrt ((k j:ℝ)+1):ℂ)*inverseWeight 3 x (up j k) := by
  rw [lowering_apply]
  change _ * ((inverseWeight 1 ∘L inverseWeight 2) x) _ = _
  rw [← inverseWeight_add]

theorem raising_weighted_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    raising j (inverseWeight 2 x) k=
      (Real.sqrt (k j:ℝ):ℂ)*inverseWeight 3 x (down j k) := by
  rcases index_cases j k with hk | ⟨l,rfl⟩
  · simp only [raising_zero j _ k hk, hk, Nat.cast_zero, Real.sqrt_zero,
      Complex.ofReal_zero, zero_mul]
  · rw [raising_up]
    change _ * ((inverseWeight 1 ∘L inverseWeight 2) x) _ = _
    rw [← inverseWeight_add, up_same, down_up]
    norm_cast
end Annihilation

namespace EntropyPhotonNumber
open Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open Annihilation WeightedGenerator
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

theorem inverse_spectralColumns_operator :
    CrossEnsemble.operator (fun r => inverseWeight 3 (G.spectralColumns r))
      (fun r => inverseWeight 3 (G.spectralColumns r))=ρ.op := by
  simp only [G.spectralColumns_inverse]
  exact CrossEnsemble.eigenEnsemble_operator G.basis G.probability
    (fun r => (G.probability_pos r).le) G.probability_sum.summable ρ.op ρ.positive.isSymmetric G.eigen

theorem weakDefect_numberMatrixUnit (t : ℝ) (j : Fin n) (a b : NumberIndex n) :
    weakDefect t G.spectralColumns j (G.annihilationMean j) (numberMatrixUnit a b)=
      (t+1:ℂ)*(Real.sqrt ((a j:ℝ)+1):ℂ)*entry ρ.op b (up j a)-
      (t:ℂ)*(Real.sqrt (b j:ℝ):ℂ)*entry ρ.op (down j b) a-
      star (G.annihilationMean j)*entry ρ.op b a :=
  WeightedGenerator.weakDefect_numberMatrixUnit t G.spectralColumns G.spectralColumns_summable
    ρ G.inverse_spectralColumns_operator j (G.annihilationMean j) a b
end EntropyPhotonNumber.GibbsData

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.BeamForms ----
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

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

theorem physical_ensemble_output (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (hτ : IsBeamSplitterOutput η ρ σ τ)
    (v : I → Fock n) (w : J → Fock n)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1)
    (hev : TraceEnsemble.operator v=ρ.op) (hew : TraceEnsemble.operator w=σ.op) :
    partialTrace (fun ij : I × J => beamUnitary η hη (tensor (v ij.1) (w ij.2)))=τ.op := by
  have hs : Summable (fun ij : I × J => ‖beamUnitary η hη (tensor (v ij.1) (w ij.2))‖^2) := by
    simpa only [LinearIsometryEquiv.norm_map] using (TraceEnsemble.hasSum_tensor_norm hv hw).summable
  apply entry_ext
  intro k l
  have he := partialTrace_entry hs k l
  simp only [beam_ensemble_entry η hη ρ σ v w hv hw hev hew] at he
  exact he.unique (hτ k l)

theorem cross_slice_eq_partialTrace (v : I → JointFock n) :
    CrossEnsemble.operator (fun ie : I × NumberIndex n => slice (v ie.1) ie.2)
      (fun ie : I × NumberIndex n => slice (v ie.1) ie.2)=partialTrace v := by
  exact (Equiv.prodComm I (NumberIndex n)).tsum_eq
    (fun ei => InnerProductSpace.rankOne ℂ (slice (v ei.2) ei.1) (slice (v ei.2) ei.1))

theorem physical_weighted_output (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (hτ : IsBeamSplitterOutput η ρ σ τ)
    (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hxn : HasSum (fun i => ‖inverseWeight 3 (x i)‖^2) 1)
    (hyn : HasSum (fun j => ‖inverseWeight 3 (y j)‖^2) 1)
    (hex : TraceEnsemble.operator (fun i => inverseWeight 3 (x i))=ρ.op)
    (hey : TraceEnsemble.operator (fun j => inverseWeight 3 (y j))=σ.op)
    (hez : TraceEnsemble.operator (fun k => inverseWeight 3 (z k))=τ.op) :
    CrossEnsemble.operator
      (fun ie : (I × J) × NumberIndex n => slice (inverse
        (beamUnitary η hη (tensorPreimage (x ie.1.1) (y ie.1.2)))) ie.2)
      (fun ie : (I × J) × NumberIndex n => slice (inverse
        (beamUnitary η hη (tensorPreimage (x ie.1.1) (y ie.1.2)))) ie.2)=
      CrossEnsemble.operator (fun k => inverseWeight 3 (z k)) (fun k => inverseWeight 3 (z k)) := by
  rw [cross_slice_eq_partialTrace (fun ij : I × J => inverse
      (beamUnitary η hη (tensorPreimage (x ij.1) (y ij.2))))]
  simp only [covariance_inverse_apply, tensorPreimage_inverse]
  change partialTrace _=TraceEnsemble.operator _
  rw [hez]
  exact physical_ensemble_output η hη ρ σ τ hτ (fun i => inverseWeight 3 (x i)) (fun j => inverseWeight 3 (y j)) hxn hyn hex hey

theorem physical_product_weak (η a b : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (hτ : IsBeamSplitterOutput η ρ σ τ)
    (j : Fin n) (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (hxn : HasSum (fun i => ‖inverseWeight 3 (x i)‖^2) 1)
    (hyn : HasSum (fun j => ‖inverseWeight 3 (y j)‖^2) 1)
    (hex : TraceEnsemble.operator (fun i => inverseWeight 3 (x i))=ρ.op)
    (hey : TraceEnsemble.operator (fun j => inverseWeight 3 (y j))=σ.op)
    (hez : TraceEnsemble.operator (fun k => inverseWeight 3 (z k))=τ.op)
    (Z : Fock n →L[ℂ] Fock n) :
    singleWeak (η*a+(1-η)*b) j z Z=
      (Real.sqrt η:ℂ)*singleWeak a j x
        (conditionalLeft (fun j => inverseWeight 3 (y j)) hyn (conjugate η hη Z))+
      (Real.sqrt (1-η):ℂ)*singleWeak b j y
        (conditionalRight (fun i => inverseWeight 3 (x i)) hxn (conjugate η hη Z)) := by
  have hs := tensorPreimage_summable x y hx hy
  have hu : Summable (fun ij : I × J => ‖beamUnitary η hη (tensorPreimage (x ij.1) (y ij.2))‖^2) := by
    simpa only [LinearIsometryEquiv.norm_map] using hs
  have he := physical_weighted_output η hη ρ σ τ hτ x y z hxn hyn hex hey hez
  rw [← output_weak _ j _ z hu hz he Z]
  exact product_weak_covariance η hη a b j x y hx hy hxn hyn Z
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

theorem single_lower_third_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    sandwich 0 3 (by omega) j x k=
      (Real.sqrt ((k j:ℝ)+1):ℂ)*inverseWeight 3 x (up j k) := by
  simp only [sandwich_apply,coefficient,inverseWeight_apply,pow_zero,one_mul]
  push_cast
  ring

theorem single_raise_third_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    creationSandwich 0 3 (by omega) j x k=
      (if k j=0 then (0:ℂ) else (Real.sqrt (k j:ℝ):ℂ))*inverseWeight 3 x (down j k) := by
  by_cases hk : k j=0
  · rw [creationSandwich_zero _ _ _ _ _ k hk,ite_eq_left hk,zero_mul]
  · rw [ite_eq_right hk]
    obtain ⟨a,rfl⟩ : ∃ a,k=up j a := ⟨down j k,(up_down j k (Nat.pos_of_ne_zero hk)).symm⟩
    rw [creationSandwich_up,down_up,up_same]
    simp only [creationCoefficient,inverseWeight_apply,pow_zero,one_mul]
    push_cast
    ring

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

-- ---- from OAI.InformationTheory.PhotonNumber.Generator ----
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

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I : Type*}

end PhysicalGenerator

namespace QuantumTrace
theorem thermalWeight_number (n : ℕ) (r : ℝ) (k : Fin n → ℕ) :
    thermalWeight n r k=(r+1)⁻¹^n*(r/(r+1))^(∑ j,k j) := by
  simp [thermalWeight,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

theorem thermalWeight_up {n : ℕ} (r : ℝ) (j : Fin n) (k : Fin n → ℕ) :
    thermalWeight n r (Annihilation.up j k)=r/(r+1)*thermalWeight n r k := by
  have hs : (∑ i,Annihilation.up j k i)=(∑ i,k i)+1 := by
    simp [Annihilation.up,Finset.sum_add_distrib]
  rw [thermalWeight_number,thermalWeight_number,hs,pow_succ]
  ring

theorem thermalWeight_balance {n : ℕ} (r : ℝ) (hr : 0<r) (j : Fin n) (k : Fin n → ℕ) :
    ((r+1:ℝ):ℂ)*(thermalWeight n r (Annihilation.up j k):ℂ)=
      (r:ℂ)*(thermalWeight n r k:ℂ) := by
  have h : (r+1)*thermalWeight n r (Annihilation.up j k)=r*thermalWeight n r k := by
    rw [thermalWeight_up]
    have hr1 : r+1≠0 := by positivity
    field_simp
  exact_mod_cast h
end QuantumTrace

namespace PhysicalGenerator

section
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ} {I : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder

namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

theorem base_density :
    CrossEnsemble.operator (PhysicalGenerator.baseFamily X.vector) (PhysicalGenerator.baseFamily X.vector)=ρ.op :=
  X.density

end WeightedColumns

end EntropyPhotonNumber

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

theorem weak_pairing_hasSum {L : Type*} (b : HilbertBasis L ℂ (Fock n))
    (r : ℝ) (j : Fin n) (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun k => inner ℂ (b k) (Z (weakOperator r j x (b k)))) (singleWeak r j x Z) := by
  have hi := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hl := CrossEnsemble.applied_summable hx (sandwich 0 3 (by omega) j)
  have hr := CrossEnsemble.applied_summable hx (creationSandwich 0 3 (by omega) j)
  have hh := ((CrossEnsemble.pairing_trace b hi hl Z).mul_left (r+1:ℂ)).sub
    ((CrossEnsemble.pairing_trace b hr hi Z).mul_left (r:ℂ))
  unfold weakOperator
  simp only [smul_apply,sub_apply,map_sub,map_smul,inner_sub_right,inner_smul_right]
  exact hh

theorem weakOperator_zero_of_geometric_diagonal (r : ℝ) (p : NumberIndex n → ℝ)
    (hb : ∀ j k, (r+1:ℂ)*(p (up j k):ℂ)=(r:ℂ)*(p k:ℂ))
    (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (he : ∀ k l, entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l=
      if k=l then (p k:ℂ) else 0) (j : Fin n) : weakOperator r j x=0 := by
  apply entry_ext
  intro k l
  rw [weakOperator_entry r j x hx,he,he]
  simp only [entry, zero_apply, inner_zero_right]
  by_cases hk : k=up j l
  · subst k
    have hc : raiseCoefficient j (up j l)=conj (lowerCoefficient j l) := by
      simp [raiseCoefficient, lowerCoefficient, up_same]
    rw [ite_eq_left rfl,down_up,ite_eq_left rfl,hc]
    calc
      _ = conj (lowerCoefficient j l)*((r+1:ℂ)*(p (up j l):ℂ)-(r:ℂ)*(p l:ℂ)) := by ring
      _ = 0 := by rw [hb]; ring
  · rw [ite_eq_right hk,mul_zero,zero_sub]
    by_cases hz : k j=0
    · simp [raiseCoefficient,hz]
    · have hd : down j k≠l := by
        intro h
        apply hk
        rw [← h,up_down j k (Nat.pos_of_ne_zero hz)]
      rw [ite_eq_right hd,mul_zero,neg_zero]

theorem weak_thermal_pairing_zero (r : ℝ) (hr : 0<r)
    (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (he : ∀ k l, entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l=
      if k=l then (thermalWeight n r k:ℂ) else 0) (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    singleWeak r j x Z=0 := by
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hh := weak_pairing_hasSum bas r j x hx Z
  have he0 := weakOperator_zero_of_geometric_diagonal r (thermalWeight n r) (fun j k => by simpa only [Complex.ofReal_add, Complex.ofReal_one] using thermalWeight_balance r hr j k) x hx he j
  have hzero : HasSum (fun _ : NumberIndex n => (0:ℂ)) 0 := hasSum_zero
  have hz : HasSum (fun _ : NumberIndex n => (0:ℂ)) (singleWeak r j x Z) := by
    simpa only [he0,zero_apply,map_zero,inner_zero_right] using hh
  exact hz.unique hzero
end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

theorem thermal_weak_zero (r : ℝ) (hr : 0<r)
    (he : ∀ k l, entry ρ.op k l=if k=l then (thermalWeight n r k:ℂ) else 0)
    (j : Fin n) (Z : Fock n →L[ℂ] Fock n) : singleWeak r j X.vector Z=0 := by
  apply PhysicalGenerator.weak_thermal_pairing_zero r hr X.vector X.summable
  intro k l
  rw [X.base_density,he]
end WeightedColumns

end EntropyPhotonNumber

namespace KrausBounded
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
end KrausBounded

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}
end BeamLadder

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

end WeightedColumns

end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end BeamLadder

namespace EntropyPhotonNumber

namespace WeightedColumns
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

end WeightedColumns

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
theorem diagonalState_entropy {n : ℕ} (p : NumberIndex n → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hs : HasSum p 1) :
    entropy (diagonalState p hp hs) = ∑' k, Real.negMulLog (p k) := by
  rw [entropy_eq_quantumTrace]
  congr 1
  funext k
  rw [QuantumTrace.entropyOperator_apply_eigenvector (diagonalState p hp hs).positive.isSymmetric
    (diagonalState_eigen p hp hs k), inner_smul_right,
    orthonormal_iff_ite.mp (numberBasis n).orthonormal k k, ite_eq_left rfl, mul_one, Complex.ofReal_re]
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
theorem numberMoment_nonneg {n : ℕ} (m : ℕ) (ρ : State n) : 0 ≤ numberMoment m ρ :=
  tsum_nonneg (fun k => mul_nonneg (by positivity) (ρ.positive.re_inner_nonneg_right _))

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

theorem State.ext_op {n : ℕ} {ρ σ : State n} (h : ρ.op = σ.op) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

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

end

variable {J : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

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

theorem beamOutput_finiteMoment {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) {m : ℕ} {ρA ρB : State n}
    (hA : FiniteMoment m ρA) (hB : FiniteMoment m ρB) : FiniteMoment m (beamOutput η hη ρA ρB) := by
  apply (finiteMoment_iff _ _).mpr
  exact (beamOutput_powerMoment_le η hη m ρA ρB).trans_lt
    (ENNReal.mul_lt_top ((finiteMoment_iff _ _).mp hA) ((finiteMoment_iff _ _).mp hB))

end EntropyPhotonNumber

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.SpectralForms ----
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
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory

namespace BKM

section
open scoped ComplexConjugate
variable {J K E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

open scoped BigOperators
variable {J : Type*}

end BKM

namespace SpectralTests
open scoped BigOperators ComplexConjugate
variable {A I P : Type*}

end SpectralTests

namespace CenteredTests
open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable [CompleteSpace E]

end CenteredTests

namespace ThermalMetric

section
open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open scoped ComplexConjugate
variable {J : Type*}

variable [DecidableEq J]

end

open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalMetric

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
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace CenteredTests
open scoped BigOperators
variable {J T E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CenteredTests

namespace ThermalMetric
open EntropyPhotonNumber DiagonalForms.System

end ThermalMetric

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

namespace Space
variable (S : Space E)
end Space

end ThermalSpectral

namespace ThermalMetric
open EntropyPhotonNumber DiagonalForms.System

end ThermalMetric

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem pairing_sub_right (u v w : I → E) (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun i => ‖w i‖^2))
    (c : ℂ) (Z : E →L[ℂ] E) :
    pairing u (fun i => v i-c • w i) Z=pairing u v Z-conj c*pairing u w Z := by
  simp only [pairing, inner_sub_left, inner_smul_left]
  rw [(pairing_summable hu hv Z).tsum_sub ((pairing_summable hu hw Z).mul_left (conj c)), tsum_mul_left]

omit [CompleteSpace E] in
theorem pairing_sub_left (u v w : I → E) (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun i => ‖w i‖^2))
    (c : ℂ) (Z : E →L[ℂ] E) :
    pairing (fun i => u i-c • v i) w Z=pairing u w Z-c*pairing v w Z := by
  simp only [pairing, map_sub, map_smul, inner_sub_right, inner_smul_right]
  rw [(pairing_summable hu hw Z).tsum_sub ((pairing_summable hv hw Z).mul_left c), tsum_mul_left]
end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation BeamLadder ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

theorem centeredLadder_lower (j : Fin n) (μ : ℂ) (x : Fock n) :
    centeredLadder j μ false x=sandwich 0 3 (by omega) j x-μ • inverseWeight 3 x := by
  have hw : inverseWeight 1 (inverseWeight 2 x)=inverseWeight 3 x := by
    change (inverseWeight 1 ∘L inverseWeight 2) x=_
    rw [← inverseWeight_add]
  simp only [centeredLadder, Bool.false_eq_true, ↓reduceIte, ContinuousLinearMap.comp_apply,
    sub_apply, smul_apply, hw]
  congr 1
  ext k
  rw [lowering_weighted_apply, single_lower_third_apply]

theorem centeredLadder_raise (j : Fin n) (μ : ℂ) (x : Fock n) :
    centeredLadder j μ true x=creationSandwich 0 3 (by omega) j x-conj μ • inverseWeight 3 x := by
  have hw : inverseWeight 1 (inverseWeight 2 x)=inverseWeight 3 x := by
    change (inverseWeight 1 ∘L inverseWeight 2) x=_
    rw [← inverseWeight_add]
  simp only [centeredLadder, ↓reduceIte, ContinuousLinearMap.comp_apply, sub_apply, smul_apply, hw]
  congr 1
  ext k
  rw [raising_weighted_apply, single_raise_third_apply]
  by_cases hk : k j=0
  · simp only [hk, Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, zero_mul, ↓reduceIte]
  · rw [ite_eq_right hk]

theorem weakDefect_uncentered (t : ℝ) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2)) (j : Fin n) (μ : ℂ) (Z : Fock n →L[ℂ] Fock n) :
    weakDefect t x j μ Z=singleWeak t j x Z-conj μ*
      CrossEnsemble.pairing (fun r => inverseWeight 3 (x r)) (fun r => inverseWeight 3 (x r)) Z := by
  have hi := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hl := CrossEnsemble.applied_summable hx (sandwich 0 3 (by omega) j)
  have hr := CrossEnsemble.applied_summable hx (creationSandwich 0 3 (by omega) j)
  simp only [weakDefect, centeredLadder_lower, centeredLadder_raise]
  rw [CrossEnsemble.pairing_sub_right _ _ _ hi hl hi,
    CrossEnsemble.pairing_sub_left _ _ _ hr hi hi]
  unfold singleWeak
  ring
end WeightedGenerator

namespace ThermalSpectral.Space
open EntropyPhotonNumber Annihilation WeightedGenerator ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} (S : Space (Fock n))

end ThermalSpectral.Space

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
theorem drift_radial (r : ℝ) (f : ℝ → ℝ) (k : NumberIndex n) :
    drift r (fun k => f (numberWeight k)) k =
      (r+1)*(numberWeight k-1)*(f (numberWeight k-1)-f (numberWeight k))+
        r*(numberWeight k-1+n)*(f (numberWeight k+1)-f (numberWeight k)) := by
  have he (j : Fin n) : (r+1)*(k j:ℝ)*(f (numberWeight (down j k))-f (numberWeight k)) =
      ((k j:ℝ)*(r+1))*(f (numberWeight k-1)-f (numberWeight k)) := by
    by_cases hk : k j=0
    · simp [hk]
    · rw [weight_down j k (Nat.pos_of_ne_zero hk)]
      ring
  simp only [drift, he, weight_up, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, numberWeight]
  ring

theorem drift_fourth (r : ℝ) (k : NumberIndex n) :
    drift r (fun k => numberWeight k^4) k=driftPolynomial n r (totalNumber k) := by
  rw [drift_radial r (fun t => t^4) k]
  simp only [driftPolynomial, numberWeight, totalNumber, Nat.cast_sum]
  ring

theorem driftPolynomial_expand (r t : ℝ) :
    driftPolynomial n r t = -4*t^4+(4*r*n+12*r-6)*t^3+
      (18*r*n+24*r-4)*t^2+(28*r*n+14*r-1)*t+15*r*n := by
  unfold driftPolynomial
  ring
end

theorem driftPolynomial_bounded (n : ℕ) (r : ℝ) :
    ∃ C : ℝ, ∀ k : ℕ, driftPolynomial n r k ≤ C := by
  obtain ⟨C,hC⟩ := negative_quartic_bounded (4*r*n+12*r-6) (18*r*n+24*r-4)
    (28*r*n+14*r-1) (15*r*n)
  exact ⟨C, fun k => (driftPolynomial_expand r k).trans_le (hC k (Nat.cast_nonneg k))⟩
end WeightedGenerator

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ}

end

open QuantumTrace Annihilation WeightedGenerator
variable {n : ℕ}

theorem polynomial_weight_six_bound (a b c d e : ℝ) (k : NumberIndex n) :
    |a*(totalNumber k:ℝ)^4+b*(totalNumber k:ℝ)^3+c*(totalNumber k:ℝ)^2+d*(totalNumber k:ℝ)+e|≤
      (|a|+|b|+|c|+|d|+|e|)*numberWeight k^6 := by
  have hp (m : ℕ) (hm : m≤6) : (totalNumber k:ℝ)^m≤numberWeight k^6 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (number_le_weight k) m).trans
      (pow_le_pow_right₀ (numberWeight_one_le k) hm)
  have h1 : (totalNumber k:ℝ)≤numberWeight k^6 := by simpa using hp 1 (by norm_num)
  have h0 : 1≤numberWeight k^6 := one_le_pow₀ (numberWeight_one_le k)
  calc
    _ ≤ |a*(totalNumber k:ℝ)^4+b*(totalNumber k:ℝ)^3+c*(totalNumber k:ℝ)^2+d*(totalNumber k:ℝ)|+|e| := abs_add_le _ _
    _ ≤ |a*(totalNumber k:ℝ)^4+b*(totalNumber k:ℝ)^3+c*(totalNumber k:ℝ)^2|+|d*(totalNumber k:ℝ)|+|e| := by gcongr; exact abs_add_le _ _
    _ ≤ |a*(totalNumber k:ℝ)^4+b*(totalNumber k:ℝ)^3|+|c*(totalNumber k:ℝ)^2|+|d*(totalNumber k:ℝ)|+|e| := by gcongr; exact abs_add_le _ _
    _ ≤ |a*(totalNumber k:ℝ)^4|+|b*(totalNumber k:ℝ)^3|+|c*(totalNumber k:ℝ)^2|+|d*(totalNumber k:ℝ)|+|e| := by gcongr; exact abs_add_le _ _
    _ = |a| *(totalNumber k:ℝ)^4+|b| *(totalNumber k:ℝ)^3+|c| *(totalNumber k:ℝ)^2+|d| *(totalNumber k:ℝ)+|e| := by simp [abs_mul,abs_pow,abs_of_nonneg (show 0≤(totalNumber k:ℝ) from Nat.cast_nonneg _)]
    _ ≤ |a| *numberWeight k^6+|b| *numberWeight k^6+|c| *numberWeight k^6+|d| *numberWeight k^6+|e| *numberWeight k^6 := by
      exact add_le_add (add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (hp 4 (by norm_num)) (abs_nonneg a))
        (mul_le_mul_of_nonneg_left (hp 3 (by norm_num)) (abs_nonneg b)))
        (mul_le_mul_of_nonneg_left (hp 2 (by norm_num)) (abs_nonneg c)))
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg d))) (by nlinarith [mul_le_mul_of_nonneg_left h0 (abs_nonneg e)])
    _ = _ := by ring

theorem drift_fourth_div_bound (r : ℝ) (k : NumberIndex n) :
    |drift r (fun k => numberWeight k^4) k/numberWeight k^6|≤fourthDriftConstant n r := by
  rw [drift_fourth,driftPolynomial_expand,abs_div,abs_of_pos (pow_pos (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k)) _)]
  apply (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k)) _)).mpr
  exact polynomial_weight_six_bound (-4) (4*r*n+12*r-6) (18*r*n+24*r-4) (28*r*n+14*r-1) (15*r*n) k

theorem fourth_diagonal_eq_one :
    diagonal (fun k : NumberIndex n => numberWeight k^4/numberWeight k^4) 1 (by norm_num)
      (fun k => by rw [div_self (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k))))]; norm_num)=
      (1 : Fock n →L[ℂ] Fock n) := by
  ext x k
  simp only [diagonal_apply,div_self (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k)))),Complex.ofReal_one,
    one_mul,one_apply_eq_self]

theorem thermalGenerator_fourth (r : ℝ) (ρ : State n) (hm : FiniteMoment 6 ρ) :
    HasSum (fun k => driftPolynomial n r (totalNumber k)*(entry ρ.op k k).re)
      (WeightedGenerator.pairing r (weightedRoot 3 ρ hm) (1 : Fock n →L[ℂ] Fock n)).re := by
  have hh := thermalGenerator_drift r ρ hm (fun k => numberWeight k^4) 1 (fourthDriftConstant n r)
    (by norm_num) (fun k => by rw [div_self (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k))))]; norm_num)
    (drift_fourth_div_bound r)
  simpa only [drift_fourth,fourth_diagonal_eq_one] using hh

theorem thermalGenerator_fourth_bound (r : ℝ) : ∃ C : ℝ, ∀ (ρ : State n) (hm : FiniteMoment 6 ρ),
    (WeightedGenerator.pairing r (weightedRoot 3 ρ hm) (1 : Fock n →L[ℂ] Fock n)).re≤C := by
  obtain ⟨C,hC⟩ := driftPolynomial_bounded n r
  refine ⟨C,fun ρ hm => ?_⟩
  have hh := thermalGenerator_fourth r ρ hm
  have hpos (k : NumberIndex n) : 0≤(entry ρ.op k k).re := ρ.positive.re_inner_nonneg_right _
  have hle := hh.summable.tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_right (hC (totalNumber k)) (hpos k))
    (ρ.trace_one.summable.mul_left C)
  simpa only [hh.tsum_eq,tsum_mul_left,ρ.trace_one.tsum_eq,mul_one] using hle
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

end EntropyPhotonNumber.Regularization

namespace EntropyPhotonNumber

section
open QuantumTrace ThermalMetric

namespace ThermalSetup
variable (P : ThermalSetup)
theorem output_op {n : ℕ} (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n) :
    ((P.reg n ζ hζ).output ρ σ).op=((1-P.κ:ℝ):ℂ) • (P.raw ρ σ).op+
      (P.κ:ℂ) • (thermalState n P.r0 P.r0_pos).op := by
  simp only [Regularization.output,reg,regularizedOutput,sub_sub_cancel,mixture,raw,middle]
end ThermalSetup

namespace WeightedColumns
variable {n : ℕ} {ρ : State n}
theorem sum_lowerEnergy (X : WeightedColumns ρ) : (∑ j, X.lowerEnergy j)=energy ρ := by
  have hh := hasSum_sum (fun j (_hj : j ∈ (Finset.univ : Finset (Fin n))) => X.lowerEnergy_hasSum j)
  have he : HasSum (fun k => (totalNumber k:ℝ)*(entry ρ.op k k).re) (∑ j, X.lowerEnergy j) := by
    simpa only [totalNumber,Nat.cast_sum,Finset.sum_mul] using hh
  exact he.tsum_eq.symm
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

theorem uniform_minimum_decay : ∃ C : ℝ, 0<C ∧ ∀ (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n),
    FiniteMoment 4 ρ → FiniteMoment 4 σ →
    (∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' →
      (P.reg n ζ hζ).objective ρ σ≤(P.reg n ζ hζ).objective ρ' σ') →
    ∃ (G1 : GibbsData n (ζ/((1+P.ε)*P.w1/h P.r1)) ρ)
      (G2 : GibbsData n (ζ/((1+P.ε)*P.w2/h P.r2)) σ),
      P.w1*((∑ j, ‖G1.defect (div_pos hζ (P.reg n ζ hζ).ha1) P.r1 P.hr1 j‖^2)+
        (∑ j, ‖G1.annihilationMean j‖^2))+
      P.w2*((∑ j, ‖G2.defect (div_pos hζ (P.reg n ζ hζ).ha2) P.r2 P.hr2 j‖^2)+
        (∑ j, ‖G2.annihilationMean j‖^2)) ≤ C*ζ := by
  obtain ⟨C1,hC1⟩ := thermalGenerator_fourth_bound (n:=n) P.r1
  obtain ⟨C2,hC2⟩ := thermalGenerator_fourth_bound (n:=n) P.r2
  refine ⟨2*(max C1 0+1+max C2 0)/P.ε,div_pos (by positivity) P.hε,?_⟩
  intro ζ hζ ρ σ hmρ hmσ hmin
  exact P.minimum_decay (max C1 0+1) (max C2 0)
    (fun ρ hm => (hC1 ρ hm).trans (by linarith [le_max_left C1 0]))
    (fun ρ hm => (hC2 ρ hm).trans (le_max_left C2 0)) ζ hζ ρ σ hmρ hmσ hmin
end ThermalSetup
end EntropyPhotonNumber

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.ThermalLimit ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace ThermalMetric
open EntropyPhotonNumber
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in

theorem column_metric_bound (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : HasSum p 1) (Z : E →L[ℂ] E) :
    Summable (fun a : J × J => p a.2*‖inner ℂ (b a.1) (Z (b a.2))‖^2) ∧
    (∑' a : J × J, p a.2*‖inner ℂ (b a.1) (Z (b a.2))‖^2) ≤ ‖Z‖^2 := by
  have hn (j : J) : ‖Z (b j)‖^2 ≤ ‖Z‖^2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) 
    simpa only [b.orthonormal.norm_eq_one, mul_one] using Z.le_opNorm (b j)
  have hsum : Summable (fun j => p j*‖Z (b j)‖^2) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hp j).le (sq_nonneg _))
      (fun j => mul_le_mul_of_nonneg_left (hn j) (hp j).le) (hs.summable.mul_right (‖Z‖^2))
  have he (j : J) : HasSum (fun i => p j*‖inner ℂ (b i) (Z (b j))‖^2)
      (p j*‖Z (b j)‖^2) := (QuantumTrace.basis_hasSum_norm_sq b (Z (b j))).mul_left (p j)
  have hadd : Summable (fun a : J × J => p a.1*‖inner ℂ (b a.2) (Z (b a.1))‖^2) := by
    apply (summable_prod_of_nonneg (fun a => mul_nonneg (hp a.1).le (sq_nonneg _))).mpr
    exact ⟨fun j => (he j).summable, by simpa only [(he _).tsum_eq] using hsum⟩
  refine ⟨hadd.prod_symm, ?_⟩
  calc
    (∑' a : J × J, p a.2*‖inner ℂ (b a.1) (Z (b a.2))‖^2) =
        ∑' a : J × J, p a.1*‖inner ℂ (b a.2) (Z (b a.1))‖^2 :=
      by simpa only [Equiv.prodComm_apply, Prod.swap] using
        (Equiv.prodComm J J).tsum_eq (fun a : J × J => p a.1*‖inner ℂ (b a.2) (Z (b a.1))‖^2)
    _ = ∑' j, p j*‖Z (b j)‖^2 := by rw [hadd.tsum_prod]; simp only [(he _).tsum_eq]
    _ ≤ ∑' j, p j*‖Z‖^2 := hsum.tsum_le_tsum
      (fun j => mul_le_mul_of_nonneg_left (hn j) (hp j).le) (hs.summable.mul_right _)
    _ = ‖Z‖^2 := by rw [tsum_mul_right, hs.tsum_eq, one_mul]

theorem bounded_matrix_bound (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : HasSum p 1) (t : ℝ) (ht : 0<t) (Z : E →L[ℂ] E) :
    (∑' a : J × J, metricCoefficient t (p a.1) (p a.2)*
      ‖inner ℂ (b a.1) (Z (b a.2))‖^2) ≤ (h t/2*(2*t+1))*‖Z‖^2 := by
  have hc := column_metric_bound b p hp hs Z
  have hca := column_metric_bound b p hp hs Z.adjoint
  have hr : Summable (fun a : J × J => p a.1*‖inner ℂ (b a.1) (Z (b a.2))‖^2) ∧
      (∑' a : J × J, p a.1*‖inner ℂ (b a.1) (Z (b a.2))‖^2) ≤ ‖Z‖^2 := by
    constructor
    · simpa only [Prod.swap, ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
        using hca.1.prod_symm
    · have he := (Equiv.prodComm J J).tsum_eq
        (fun a : J × J => p a.2*‖inner ℂ (b a.1) (Z.adjoint (b a.2))‖^2)
      have hb := hca.2
      rw [← he] at hb
      simpa only [Equiv.prodComm_apply, Prod.swap, ContinuousLinearMap.adjoint_inner_right,
        norm_inner_symm, LinearIsometryEquiv.norm_map] using hb
  have hh := bounded_matrix_summable b p hp hs.summable t ht Z
  have hb := (((hr.1.mul_left t).add (hc.1.mul_left (t+1))).mul_left (h t/2))
  calc
    _ ≤ ∑' a : J × J, h t/2*(t*(p a.1*‖inner ℂ (b a.1) (Z (b a.2))‖^2)+
        (t+1)*(p a.2*‖inner ℂ (b a.1) (Z (b a.2))‖^2)) := by
      apply hh.tsum_le_tsum _ hb
      intro a
      have ha := DiagonalForms.System.logMean_le_arithmetic (mul_pos ht (hp a.1))
        (mul_pos (by positivity : 0<t+1) (hp a.2))
      have hm : metricCoefficient t (p a.1) (p a.2) =
          h t*DiagonalForms.System.logMean (t*p a.1) ((t+1)*p a.2) := by
        rw [metricCoefficient, mul_assoc, tilted_logMean ht (hp _) (hp _)]
      rw [hm]
      have he := mul_le_mul_of_nonneg_left ha (h_pos ht).le
      nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg ‖inner ℂ (b a.1) (Z (b a.2))‖)]
    _ = h t/2*(t*(∑' a : J × J, p a.1*‖inner ℂ (b a.1) (Z (b a.2))‖^2)+
        (t+1)*(∑' a : J × J, p a.2*‖inner ℂ (b a.1) (Z (b a.2))‖^2)) := by
      rw [tsum_mul_left, (hr.1.mul_left t).tsum_add (hc.1.mul_left (t+1)),
        tsum_mul_left, tsum_mul_left]
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left hr.2 ht.le
      have h₂ := mul_le_mul_of_nonneg_left hc.2 (by linarith : 0≤t+1)
      have hc0 : 0 ≤ h t/2 := div_nonneg (h_pos ht).le (by norm_num)
      have h₃ := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hc0
      nlinarith
end ThermalMetric

namespace EntropyPhotonNumber.GibbsData
open WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

theorem full_defect_on_observable (hk : 0<k) (t : ℝ) (ht : 0<t) (j : Fin n)
    (Z : Fock n →L[ℂ] Fock n) :
    defectFunctional t ht G.probability G.probability_pos (G.centeredMatrix j)
      (G.centeredMatrix_defect_summable hk t j) (G.observableVector t ht Z)=
      weakDefect t G.spectralColumns j (G.annihilationMean j) Z := by
  exact (defectVector_pairing t ht G.probability G.probability_pos (G.centeredMatrix j)
    (G.centeredMatrix_defect_summable hk t j)
    (fun a => inner ℂ (G.basis a.1) (Z (G.basis a.2)))
    (bounded_matrix_summable G.basis G.probability G.probability_pos
      G.probability_sum.summable t ht Z)).unique
    (weakDefect_spectral G.basis G.probability G.probability_pos G.spectralColumns
      G.spectralColumns_summable G.spectralColumns_inverse t j (G.annihilationMean j) Z)

theorem observableVector_bound (t : ℝ) (ht : 0<t) (Z : Fock n →L[ℂ] Fock n) :
    ‖G.observableVector t ht Z‖^2 ≤ (h t/2*(2*t+1))*‖Z‖^2 := by
  rw [observableVector, matrixVector, weightedVector_norm_sq]
  exact bounded_matrix_bound G.basis G.probability G.probability_pos G.probability_sum t ht Z

theorem weakDefect_bound (hk : 0<k) (t : ℝ) (ht : 0<t) (j : Fin n)
    (Z : Fock n →L[ℂ] Fock n) :
    ‖weakDefect t G.spectralColumns j (G.annihilationMean j) Z‖^2 ≤
      ‖G.defect hk t ht j‖^2*((h t/2*(2*t+1))*‖Z‖^2) := by
  let F := defectFunctional t ht G.probability G.probability_pos (G.centeredMatrix j)
      (G.centeredMatrix_defect_summable hk t j)
  have hn : ‖F‖=‖G.defect hk t ht j‖ := by
    symm
    exact defectFunctional_restrict_norm t ht G.probability G.probability_pos
      (G.centeredMatrix j) _ _
      (defectVector_mem_centeredSpace t ht G.probability G.probability_pos
        G.probability_sum.summable (G.centeredMatrix j) _ (G.centeredMatrix_mean_zero j))
  rw [← G.full_defect_on_observable hk t ht j Z]
  calc
    _ ≤ (‖F‖*‖G.observableVector t ht Z‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (F.le_opNorm _) 2
    _ = ‖G.defect hk t ht j‖^2*‖G.observableVector t ht Z‖^2 := by rw [mul_pow, hn]
    _ ≤ _ := mul_le_mul_of_nonneg_left (G.observableVector_bound t ht Z) (sq_nonneg _)
end EntropyPhotonNumber.GibbsData

namespace ThermalRecurrence

section
variable {J : Type*} [Fintype J] [DecidableEq J]

end

end ThermalRecurrence

namespace EntropyPhotonNumber
open Filter Topology Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ}

theorem entry_tendsto {ρ : ℕ → State n} {σ : State n}
    (he : Tendsto (fun m => (ρ m).op) atTop (𝓝 σ.op)) (a b : NumberIndex n) :
    Tendsto (fun m => entry (ρ m).op a b) atTop (𝓝 (entry σ.op a b)) :=
  tendsto_const_nhds.inner
    (((ContinuousLinearMap.apply ℂ (Fock n) (numberKet b)).continuous.tendsto _).comp he)

theorem state_entry_star (ρ : State n) (a b : NumberIndex n) :
    entry ρ.op b a=conj (entry ρ.op a b) := by
  change inner ℂ (numberKet b) (ρ.op (numberKet a))= _
  calc
    _ = inner ℂ (ρ.op (numberKet b)) (numberKet a) :=
      (ρ.positive.isSymmetric (numberKet b) (numberKet a)).symm
    _ = _ := (inner_conj_symm _ _).symm

theorem weakDefect_tendsto {ρ : ℕ → State n} {k : ℕ → ℝ}
    (G : ∀ m, GibbsData n (k m) (ρ m)) (hk : ∀ m, 0<k m)
    (t : ℝ) (ht : 0<t) (j : Fin n)
    (hq : Tendsto (fun m => ‖(G m).defect (hk m) t ht j‖) atTop (𝓝 0))
    (Z : Fock n →L[ℂ] Fock n) :
    Tendsto (fun m => weakDefect t (G m).spectralColumns j ((G m).annihilationMean j) Z)
      atTop (𝓝 0) := by
  have hsq : Tendsto (fun m => ‖weakDefect t (G m).spectralColumns j
      ((G m).annihilationMean j) Z‖^2) atTop (𝓝 0) := by
    exact squeeze_zero (fun _ => sq_nonneg _)
      (fun m => (G m).weakDefect_bound (hk m) t ht j Z)
      (by simpa only [zero_pow (by decide : 2≠0), zero_mul] using
        (hq.pow 2).mul_const ((h t/2*(2*t+1))*‖Z‖^2))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

theorem thermal_limit_entries {ρ : ℕ → State n} {k : ℕ → ℝ} {σ : State n}
    (G : ∀ m, GibbsData n (k m) (ρ m)) (hk : ∀ m, 0<k m)
    (t : ℝ) (ht : 0<t)
    (he : Tendsto (fun m => (ρ m).op) atTop (𝓝 σ.op))
    (hμ : ∀ j, Tendsto (fun m => (G m).annihilationMean j) atTop (𝓝 0))
    (hq : ∀ j, Tendsto (fun m => ‖(G m).defect (hk m) t ht j‖) atTop (𝓝 0))
    (p b : NumberIndex n) :
    entry σ.op p b = if p=b then (QuantumTrace.thermalWeight n t p:ℂ) else 0 := by
  have hz (j : Fin n) (a b : NumberIndex n) :
      (t+1:ℂ)*(Real.sqrt ((a j:ℝ)+1):ℂ)*entry σ.op b (up j a)-
        (t:ℂ)*(Real.sqrt (b j:ℝ):ℂ)*entry σ.op (down j b) a=0 := by
    have hl := weakDefect_tendsto G hk t ht j (hq j) (numberMatrixUnit a b)
    simp only [(G _).weakDefect_numberMatrixUnit] at hl
    have hr := (((entry_tendsto he b (up j a)).const_mul
      ((t+1:ℂ)*(Real.sqrt ((a j:ℝ)+1):ℂ))).sub
      ((entry_tendsto he (down j b) a).const_mul ((t:ℂ)*(Real.sqrt (b j:ℝ):ℂ)))).sub
      ((Complex.continuous_conj.tendsto 0 |>.comp (hμ j)).mul (entry_tendsto he b a))
    have hh := tendsto_nhds_unique hr hl
    simpa only [map_zero, zero_mul, sub_zero] using hh
  have hb : ThermalRecurrence.Balance t (entry σ.op) := by
    intro j p b hp
    have hh := congrArg conj (hz j (down j p) b)
    have hdown : (down j p j:ℝ)+1=p j := by
      simp only [down, Function.update_self]
      exact_mod_cast Nat.sub_add_cancel hp
    have hlow (a : NumberIndex n) : ThermalRecurrence.lower a j=down j a := rfl
    simp only [map_sub, map_mul, map_add, map_one, Complex.conj_ofReal, map_zero,
      ← state_entry_star, up_down j p hp, hdown] at hh
    simpa only [hlow, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_add,
      Complex.ofReal_one, mul_assoc] using sub_eq_zero.mp hh
  exact ThermalRecurrence.unique_thermal_matrix n ht hb (state_entry_star σ) σ.trace_one p b
end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate Topology

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder

theorem thermalState_energy (n : ℕ) (r : ℝ) (hr : 0<r) :
    energy (thermalState n r hr)=(n:ℝ)*r := by
  let X := WeightedColumns.canonical (thermalState n r hr) (thermalState_finiteMoment n 6 r hr)
  rw [← X.sum_lowerEnergy]
  simp only [X.thermal_lowerEnergy r hr (Regularization.thermal_state_diagonal r hr),
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem thermalState_entropy (n : ℕ) (r : ℝ) (hr : 0<r) :
    entropy (thermalState n r hr)=(n:ℝ)*g r := by
  have hE : Summable (fun k : NumberIndex n => (∑ j, (k j:ℝ))*thermalWeight n r k) := by
    simpa only [FiniteEnergy,thermalState,diagonalState_diagonal,totalNumber,Nat.cast_sum] using
      thermalState_finiteEnergy n r hr
  have hs := tsum_thermal_crossEntropy (hasSum_thermalWeight n hr) hE hr
  have he : (∑' k : NumberIndex n, (∑ j, (k j:ℝ))*thermalWeight n r k)=(n:ℝ)*r := by
    simpa only [energy,thermalState,diagonalState_diagonal,totalNumber,Nat.cast_sum] using
      thermalState_energy n r hr
  rw [he] at hs
  rw [thermalState,diagonalState_entropy]
  have hh : (∑' k : NumberIndex n, Real.negMulLog (thermalWeight n r k))=
      ∑' k : NumberIndex n, thermalWeight n r k*(-Real.log (thermalWeight n r k)) := by
    apply tsum_congr
    intro k
    simp only [Real.negMulLog_def]
    ring
  rw [hh,hs]
  unfold g
  rw [Real.log_div (by linarith : r+1≠0) hr.ne']
  ring

theorem thermal_beamOutput {n : ℕ} (η a b : ℝ) (hη : η∈Set.Icc 0 1)
    (ha : 0<a) (hb : 0<b) (hc : 0<η*a+(1-η)*b) :
    beamOutput η hη (thermalState n a ha) (thermalState n b hb)=
      thermalState n (η*a+(1-η)*b) hc := by
  let ρ := thermalState n a ha
  let σ := thermalState n b hb
  let τ := beamOutput η hη ρ σ
  let X := WeightedColumns.canonical ρ (thermalState_finiteMoment n 6 a ha)
  let Y := WeightedColumns.canonical σ (thermalState_finiteMoment n 6 b hb)
  let T := WeightedColumns.canonical τ (beamOutput_finiteMoment η hη
    (thermalState_finiteMoment n 6 a ha) (thermalState_finiteMoment n 6 b hb))
  let c := η*a+(1-η)*b
  have hz (j : Fin n) (p q : NumberIndex n) :
      (c+1:ℂ)*(Real.sqrt ((p j:ℝ)+1):ℂ)*entry τ.op q (up j p)-
        (c:ℂ)*(Real.sqrt (q j:ℝ):ℂ)*entry τ.op (down j q) p=0 := by
    have hh := physical_product_weak η a b hη ρ σ τ (beamOutput_spec _ _ _ _) j
      X.vector Y.vector T.vector X.summable Y.summable T.summable X.normalized Y.normalized
      X.density Y.density T.density (numberMatrixUnit p q)
    rw [X.thermal_weak_zero a ha (Regularization.thermal_state_diagonal a ha),
      Y.thermal_weak_zero b hb (Regularization.thermal_state_diagonal b hb),mul_zero,mul_zero,add_zero] at hh
    have hw := WeightedGenerator.weakDefect_numberMatrixUnit c T.vector T.summable τ T.base_density j 0 p q
    rw [WeightedGenerator.weakDefect_uncentered c T.vector T.summable j 0,
      map_zero,zero_mul,sub_zero] at hw
    simpa only [map_zero,zero_mul,sub_zero] using hw.symm.trans hh
  have hbalance : ThermalRecurrence.Balance c (entry τ.op) := by
    intro j p q hp
    have hh := congrArg conj (hz j (down j p) q)
    have hdown : (down j p j:ℝ)+1=p j := by
      simp only [down,Function.update_self]
      exact_mod_cast Nat.sub_add_cancel hp
    have hlow (k : NumberIndex n) : ThermalRecurrence.lower k j=down j k := rfl
    simp only [map_sub,map_mul,map_add,map_one,Complex.conj_ofReal,map_zero,
      ← state_entry_star,up_down j p hp,hdown] at hh
    simpa only [hlow,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_add,
      Complex.ofReal_one,mul_assoc] using sub_eq_zero.mp hh
  apply State.ext_op
  apply entry_ext
  intro p q
  exact (ThermalRecurrence.unique_thermal_matrix n hc hbalance (state_entry_star τ) τ.trace_one p q).trans
    (Regularization.thermal_state_diagonal c hc p q).symm

namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)
theorem output_thermal (ζ : ℝ) (hζ : 0<ζ) :
    (P.reg n ζ hζ).output (thermalState n P.r1 P.hr1) (thermalState n P.r2 P.hr2)=
      thermalState n P.r0 P.r0_pos := by
  have hm : 0<P.η*P.r1+(1-P.η)*P.r2 := add_pos (mul_pos P.hη.1 P.hr1)
    (mul_pos (sub_pos.mpr P.hη.2) P.hr2)
  have hh : P.raw (thermalState n P.r1 P.hr1) (thermalState n P.r2 P.hr2)=
      thermalState n P.r0 P.r0_pos := by
    unfold raw middle
    rw [thermal_beamOutput P.η P.r1 P.r2 P.η_mem P.hr1 P.hr2 hm]
    exact thermal_beamOutput P.θ _ P.d P.θ_mem hm P.hd P.r0_pos
  apply State.ext_op
  rw [P.output_op,hh]
  apply ContinuousLinearMap.ext
  intro vector
  simp only [add_apply,smul_apply]
  rw [← add_smul]
  norm_num
end ThermalSetup
end

section
open QuantumTrace Annihilation Filter ThermalMetric

theorem op_mem_energySet {n : ℕ} {ρ : State n} {E : ℝ}
    (hρ : FiniteEnergy ρ) (hb : energy ρ≤E) : ρ.op∈energySet (numberBasis n) E := by
  refine ⟨ρ.positive,trace_one_numberBasis ρ,?_,?_⟩
  · simpa only [FiniteEnergy,totalNumber,Nat.cast_sum,entry,numberBasis_apply] using hρ
  · simpa only [energy,totalNumber,Nat.cast_sum,entry,numberBasis_apply] using hb

theorem pair_energy_subsequence {n : ℕ} {ρ σ : ℕ → State n} {E : ℝ}
    (hρ : ∀ m, FiniteEnergy (ρ m)) (hσ : ∀ m, FiniteEnergy (σ m))
    (hbρ : ∀ m, energy (ρ m)≤E) (hbσ : ∀ m, energy (σ m)≤E) :
    ∃ (α β : State n), FiniteEnergy α ∧ FiniteEnergy β ∧ energy α≤E ∧ energy β≤E ∧
      ∃ f : ℕ → ℕ, StrictMono f ∧
        Tendsto (fun m => (ρ (f m)).op) atTop (𝓝 α.op) ∧
        Tendsto (fun m => (σ (f m)).op) atTop (𝓝 β.op) := by
  have hc := (energySet_isCompact (numberBasis n) E).prod (energySet_isCompact (numberBasis n) E)
  obtain ⟨p,hp,f,hf,hlim⟩ := hc.tendsto_subseq (fun m =>
    (show ((ρ m).op,(σ m).op)∈energySet (numberBasis n) E ×ˢ energySet (numberBasis n) E from
      ⟨op_mem_energySet (hρ m) (hbρ m),op_mem_energySet (hσ m) (hbσ m)⟩))
  let α : State n := ⟨p.1,hp.1.1,by simpa only [numberBasis_apply,entry] using hp.1.2.1⟩
  let β : State n := ⟨p.2,hp.2.1,by simpa only [numberBasis_apply,entry] using hp.2.2.1⟩
  refine ⟨α,β,?_,?_,?_,?_,f,hf,?_,?_⟩
  · simpa only [FiniteEnergy,totalNumber,Nat.cast_sum,entry,numberBasis_apply,α] using hp.1.2.2.1
  · simpa only [FiniteEnergy,totalNumber,Nat.cast_sum,entry,numberBasis_apply,β] using hp.2.2.2.1
  · simpa only [energy,totalNumber,Nat.cast_sum,entry,numberBasis_apply,α] using hp.1.2.2.2
  · simpa only [energy,totalNumber,Nat.cast_sum,entry,numberBasis_apply,β] using hp.2.2.2.2
  · simpa only [Function.comp_def,α] using (continuous_fst.tendsto p).comp hlim
  · simpa only [Function.comp_def,β] using (continuous_snd.tendsto p).comp hlim

theorem thermal_limit_state {n : ℕ} {ρ : ℕ → State n} {k : ℕ → ℝ} {σ : State n}
    (G : ∀ m, GibbsData n (k m) (ρ m)) (hk : ∀ m, 0<k m)
    (t : ℝ) (ht : 0<t)
    (he : Tendsto (fun m => (ρ m).op) atTop (𝓝 σ.op))
    (hμ : ∀ j, Tendsto (fun m => (G m).annihilationMean j) atTop (𝓝 0))
    (hq : ∀ j, Tendsto (fun m => ‖(G m).defect (hk m) t ht j‖) atTop (𝓝 0)) :
    σ=thermalState n t ht := by
  apply State.ext_op
  apply entry_ext
  intro p b
  exact (thermal_limit_entries G hk t ht he hμ hq p b).trans
    (Regularization.thermal_state_diagonal t ht p b).symm

theorem component_tendsto_zero {n : ℕ} {v : ℕ → Fin n → ℝ} {B : ℕ → ℝ}
    {w : ℝ} (hw : 0<w) (hv : ∀ m j, 0≤v m j)
    (hb : ∀ m, w*(∑ j, (v m j)^2)≤B m) (hB : Tendsto B atTop (𝓝 0))
    (j : Fin n) : Tendsto (fun m => v m j) atTop (𝓝 0) := by
  have hsq : Tendsto (fun m => (v m j)^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _)
      (fun m => (show (v m j)^2≤B m/w from (le_div_iff₀ hw).mpr ?_))
      (by simpa only [zero_div] using hB.div_const w)
    have hh := Finset.single_le_sum (fun i (_hi : i∈(Finset.univ : Finset (Fin n))) => sq_nonneg (v m i))
      (Finset.mem_univ j)
    nlinarith [mul_le_mul_of_nonneg_left hh hw.le,hb m]
  simpa only [Function.comp_def,Real.sqrt_sq (hv _ _),Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq

theorem weighted_pair_components {w u a b c d B : ℝ} (hw : 0≤w) (hu : 0≤u)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d)
    (hh : w*(a+b)+u*(c+d)≤B) : w*a≤B ∧ w*b≤B ∧ u*c≤B ∧ u*d≤B := by
  have hwa := mul_nonneg hw ha
  have hwb := mul_nonneg hw hb
  have huc := mul_nonneg hu hc
  have hud := mul_nonneg hu hd
  simp only [mul_add] at hh
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem four_components_tendsto_zero {n : ℕ} {q1 q2 μ1 μ2 : ℕ → Fin n → ℝ}
    {w1 w2 : ℝ} (hw1 : 0<w1) (hw2 : 0<w2) {B : ℕ → ℝ}
    (hq1 : ∀ m j, 0≤q1 m j) (hq2 : ∀ m j, 0≤q2 m j)
    (hμ1 : ∀ m j, 0≤μ1 m j) (hμ2 : ∀ m j, 0≤μ2 m j)
    (hb : ∀ m, w1*((∑ j, (q1 m j)^2)+(∑ j, (μ1 m j)^2))+
      w2*((∑ j, (q2 m j)^2)+(∑ j, (μ2 m j)^2))≤B m)
    (hB : Tendsto B atTop (𝓝 0)) :
    (∀ j, Tendsto (fun m => q1 m j) atTop (𝓝 0)) ∧
    (∀ j, Tendsto (fun m => q2 m j) atTop (𝓝 0)) ∧
    (∀ j, Tendsto (fun m => μ1 m j) atTop (𝓝 0)) ∧
    (∀ j, Tendsto (fun m => μ2 m j) atTop (𝓝 0)) := by
  have hn (v : ℕ → Fin n → ℝ) (m) : 0≤∑ j, (v m j)^2 :=
    Finset.sum_nonneg (fun _j _ => sq_nonneg _)
  have hh (m) := weighted_pair_components hw1.le hw2.le
    (hn q1 m) (hn μ1 m) (hn q2 m) (hn μ2 m) (hb m)
  exact ⟨component_tendsto_zero hw1 hq1 (fun m => (hh m).1) hB,
    component_tendsto_zero hw2 hq2 (fun m => (hh m).2.2.1) hB,
    component_tendsto_zero hw1 hμ1 (fun m => (hh m).2.1) hB,
    component_tendsto_zero hw2 hμ2 (fun m => (hh m).2.2.2) hB⟩

theorem pair_thermal_subsequence {n : ℕ} {ρ σ : ℕ → State n} {k1 k2 : ℕ → ℝ}
    (G1 : ∀ m, GibbsData n (k1 m) (ρ m)) (G2 : ∀ m, GibbsData n (k2 m) (σ m))
    (hk1 : ∀ m, 0<k1 m) (hk2 : ∀ m, 0<k2 m) (r1 r2 : ℝ) (hr1 : 0<r1) (hr2 : 0<r2)
    (hq1 : ∀ j, Tendsto (fun m => ‖(G1 m).defect (hk1 m) r1 hr1 j‖) atTop (𝓝 0))
    (hq2 : ∀ j, Tendsto (fun m => ‖(G2 m).defect (hk2 m) r2 hr2 j‖) atTop (𝓝 0))
    (hμ1 : ∀ j, Tendsto (fun m => ‖(G1 m).annihilationMean j‖) atTop (𝓝 0))
    (hμ2 : ∀ j, Tendsto (fun m => ‖(G2 m).annihilationMean j‖) atTop (𝓝 0))
    (hρ : ∀ m, FiniteEnergy (ρ m)) (hσ : ∀ m, FiniteEnergy (σ m))
    {E : ℝ} (hbρ : ∀ m, energy (ρ m)≤E) (hbσ : ∀ m, energy (σ m)≤E) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      Tendsto (fun m => (ρ (f m)).op) atTop (𝓝 (thermalState n r1 hr1).op) ∧
      Tendsto (fun m => (σ (f m)).op) atTop (𝓝 (thermalState n r2 hr2).op) := by
  obtain ⟨α,β,_hα,_hβ,_hbα,_hbβ,f,hf,hlim1,hlim2⟩ := pair_energy_subsequence hρ hσ hbρ hbσ
  have he1 := thermal_limit_state (fun m => G1 (f m)) (fun m => hk1 (f m)) r1 hr1 hlim1
    (fun j => (tendsto_zero_iff_norm_tendsto_zero.mpr (hμ1 j)).comp hf.tendsto_atTop)
    (fun j => (hq1 j).comp hf.tendsto_atTop)
  have he2 := thermal_limit_state (fun m => G2 (f m)) (fun m => hk2 (f m)) r2 hr2 hlim2
    (fun j => (tendsto_zero_iff_norm_tendsto_zero.mpr (hμ2 j)).comp hf.tendsto_atTop)
    (fun j => (hq2 j).comp hf.tendsto_atTop)
  exact ⟨f,hf,by simpa only [he1] using hlim1,by simpa only [he2] using hlim2⟩

namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)
theorem minimum_thermal_subsequence {ζ : ℕ → ℝ} (hζ : ∀ m, 0<ζ m)
    (hzlim : Tendsto ζ atTop (𝓝 0)) {ρ σ : ℕ → State n}
    (h4ρ : ∀ m, FiniteMoment 4 (ρ m)) (h4σ : ∀ m, FiniteMoment 4 (σ m))
    (hmin : ∀ m ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' →
      (P.reg n (ζ m) (hζ m)).objective (ρ m) (σ m)≤(P.reg n (ζ m) (hζ m)).objective ρ' σ')
    {E : ℝ} (hbρ : ∀ m, energy (ρ m)≤E) (hbσ : ∀ m, energy (σ m)≤E) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      Tendsto (fun m => (ρ (f m)).op) atTop (𝓝 (thermalState n P.r1 P.hr1).op) ∧
      Tendsto (fun m => (σ (f m)).op) atTop (𝓝 (thermalState n P.r2 P.hr2).op) := by
  obtain ⟨C,_hC,hdec⟩ := P.uniform_minimum_decay (n:=n)
  choose G1 G2 hG using fun m => hdec (ζ m) (hζ m) (ρ m) (σ m) (h4ρ m) (h4σ m) (hmin m)
  let k1 := fun m => ζ m/((1+P.ε)*P.w1/h P.r1)
  let k2 := fun m => ζ m/((1+P.ε)*P.w2/h P.r2)
  have hk1 (m) : 0<k1 m := div_pos (hζ m) (P.reg n (ζ m) (hζ m)).ha1
  have hk2 (m) : 0<k2 m := div_pos (hζ m) (P.reg n (ζ m) (hζ m)).ha2
  have hB : Tendsto (fun m => C*ζ m) atTop (𝓝 0) := by
    simpa only [mul_zero] using hzlim.const_mul C
  obtain ⟨hq1,hq2,hμ1,hμ2⟩ := four_components_tendsto_zero (q1:=fun m j => ‖(G1 m).defect (hk1 m) P.r1 P.hr1 j‖)
    (q2:=fun m j => ‖(G2 m).defect (hk2 m) P.r2 P.hr2 j‖)
    (μ1:=fun m j => ‖(G1 m).annihilationMean j‖)
    (μ2:=fun m j => ‖(G2 m).annihilationMean j‖) P.w1_pos P.w2_pos
    (fun m j => norm_nonneg ((G1 m).defect (hk1 m) P.r1 P.hr1 j))
    (fun m j => norm_nonneg ((G2 m).defect (hk2 m) P.r2 P.hr2 j))
    (fun m j => norm_nonneg ((G1 m).annihilationMean j))
    (fun m j => norm_nonneg ((G2 m).annihilationMean j)) hG hB
  exact pair_thermal_subsequence G1 G2 hk1 hk2 P.r1 P.r2 P.hr1 P.hr2 hq1 hq2 hμ1 hμ2
    (fun m => finiteMoment_finiteEnergy (by decide : 1≤4) (h4ρ m))
    (fun m => finiteMoment_finiteEnergy (by decide : 1≤4) (h4σ m)) hbρ hbσ
end ThermalSetup
end

open QuantumTrace ThermalMetric Filter

theorem thermalRelative_nonneg {n : ℕ} {r : ℝ} (hr : 0<r) {ρ : State n}
    (hρ : FiniteEnergy ρ) : 0≤thermalRelative r ρ := by
  have hh := entropy_le_thermal_crossEntropy (numberBasis n) ρ.positive
    (trace_one_numberBasis ρ)
    (by simpa only [FiniteEnergy,totalNumber,Nat.cast_sum,entry,numberBasis_apply] using hρ) hr
  rw [← entropy_eq_quantumTrace] at hh
  have hh' : entropy ρ≤n*Real.log (r+1)+energy ρ*Real.log ((r+1)/r) := by
    simpa only [energy,totalNumber,Nat.cast_sum,entry,numberBasis_apply] using hh
  rw [Real.log_div (by linarith : r+1≠0) hr.ne'] at hh'
  unfold thermalRelative h
  nlinarith

namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)
theorem objective_offset (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n) :
    (P.reg n ζ hζ).objective ρ σ+P.offset n=
      P.entropyPart ρ σ+P.penalty ρ σ+ζ*(numberMoment 4 ρ+numberMoment 4 σ) := by
  unfold Regularization.objective entropyPart penalty offset thermalRelative
  change (1/h P.r0)*entropy (P.out ρ σ)-((1+P.ε)*P.w1/h P.r1)*entropy ρ-
    ((1+P.ε)*P.w2/h P.r2)*entropy σ+(P.ε*P.w1*energy ρ+ζ*numberMoment 4 ρ)+
    (P.ε*P.w2*energy σ+ζ*numberMoment 4 σ)+_= _
  field_simp [(h_pos P.hr1).ne', (h_pos P.hr2).ne', (h_pos P.r0_pos).ne']
  ring

theorem penalty_nonneg {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    0≤P.penalty ρ σ :=
  mul_nonneg P.hε.le (add_nonneg
    (mul_nonneg (div_pos P.w1_pos (h_pos P.hr1)).le (thermalRelative_nonneg P.hr1 hρ))
    (mul_nonneg (div_pos P.w2_pos (h_pos P.hr2)).le (thermalRelative_nonneg P.hr2 hσ)))

theorem entropyPart_tendsto {A : Type*} {l : Filter A} {ρ σ : A → State n}
    {E : ℝ} (hρ : ∀ a, FiniteEnergy (ρ a)) (hσ : ∀ a, FiniteEnergy (σ a))
    (hbρ : ∀ a, energy (ρ a)≤E) (hbσ : ∀ a, energy (σ a)≤E)
    (hlimρ : Tendsto (fun a => (ρ a).op) l (𝓝 (thermalState n P.r1 P.hr1).op))
    (hlimσ : Tendsto (fun a => (σ a).op) l (𝓝 (thermalState n P.r2 P.hr2).op)) :
    Tendsto (fun a => P.entropyPart (ρ a) (σ a)) l (𝓝 0) := by
  let E' := max E (max ((n:ℝ)*P.r1) ((n:ℝ)*P.r2))
  have hb1 (a) : energy (ρ a)≤E' := (hbρ a).trans (le_max_left _ _)
  have hb2 (a) : energy (σ a)≤E' := (hbσ a).trans (le_max_left _ _)
  have hc1 : energy (thermalState n P.r1 P.hr1)≤E' := by
    rw [thermalState_energy]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hc2 : energy (thermalState n P.r2 P.hr2)≤E' := by
    rw [thermalState_energy]; exact (le_max_right _ _).trans (le_max_right _ _)
  have h1 := tendsto_entropy hρ (thermalState_finiteEnergy n _ P.hr1) hb1 hc1 hlimρ
  have h2 := tendsto_entropy hσ (thermalState_finiteEnergy n _ P.hr2) hb2 hc2 hlimσ
  let R := P.reg n 1 zero_lt_one
  have h0 : Tendsto (fun a => entropy (P.out (ρ a) (σ a))) l
      (𝓝 (entropy (P.out (thermalState n P.r1 P.hr1) (thermalState n P.r2 P.hr2)))) := by
    apply tendsto_entropy (E:=E'+E'+energy R.τD+energy R.τ0)
      (fun a => regularizedOutput_finiteEnergy R.η R.δ R.κ R.hη R.hδ R.hκ R.finiteD R.finite0 (hρ a) (hσ a))
      (regularizedOutput_finiteEnergy R.η R.δ R.κ R.hη R.hδ R.hκ R.finiteD R.finite0
        (thermalState_finiteEnergy n _ P.hr1) (thermalState_finiteEnergy n _ P.hr2))
    · intro a
      exact (regularizedOutput_energy_bound R.η R.δ R.κ R.hη R.hδ R.hκ R.finiteD R.finite0 (hρ a) (hσ a)).trans
        (by linarith [hb1 a,hb2 a])
    · exact (regularizedOutput_energy_bound R.η R.δ R.κ R.hη R.hδ R.hκ R.finiteD R.finite0
        (thermalState_finiteEnergy n _ P.hr1) (thermalState_finiteEnergy n _ P.hr2)).trans
        (by linarith)
    · exact tendsto_regularizedOutput R.η R.δ R.κ R.hη R.hδ R.hκ R.τD R.τ0 hlimρ hlimσ
  have he := (((h0.sub_const (n*g P.r0)).div_const (h P.r0)).sub
    ((h1.sub_const (n*g P.r1)).const_mul P.w1 |>.div_const (h P.r1))).sub
    ((h2.sub_const (n*g P.r2)).const_mul P.w2 |>.div_const (h P.r2))
  simpa only [out,P.output_thermal,thermalState_entropy,sub_self,mul_zero,zero_div,entropyPart] using he

theorem base_nonnegative {ρw σw : State n} (hw1 : FiniteMoment 4 ρw) (hw2 : FiniteMoment 4 σw) :
    0≤P.entropyPart ρw σw+P.penalty ρw σw := by
  let ζ : ℕ → ℝ := fun m => 1/((m:ℝ)+1)
  have hζ (m) : 0<ζ m := by dsimp [ζ]; positivity
  have hζ1 (m) : ζ m≤1 := by
    dsimp [ζ]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hzlim : Tendsto ζ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose ρ σ h4ρ h4σ hminw hmin using fun m => (P.reg n (ζ m) (hζ m)).exists_minimum ρw σw hw1 hw2
  have hρ (m) := finiteMoment_finiteEnergy (by decide : 1≤4) (h4ρ m)
  have hσ (m) := finiteMoment_finiteEnergy (by decide : 1≤4) (h4σ m)
  let R := P.reg n 1 zero_lt_one
  let C := R.objective ρw σw
  have hbmin (m) : (P.reg n (ζ m) (hζ m)).objective (ρ m) (σ m)≤C := by
    apply (hminw m).trans
    have hzm := mul_le_mul_of_nonneg_right (hζ1 m)
      (add_nonneg (numberMoment_nonneg 4 ρw) (numberMoment_nonneg 4 σw))
    have h1 := P.objective_offset (ζ m) (hζ m) ρw σw
    have h2 := P.objective_offset 1 zero_lt_one ρw σw
    dsimp [C,R]
    linarith
  let E := max (2*(C+R.entropyConstant)/R.b1) (2*(C+R.entropyConstant)/R.b2)
  have hbρ (m) : energy (ρ m)≤E := by
    have hh := (P.reg n (ζ m) (hζ m)).sublevel_bounds C (ρ m) (σ m) (hρ m) (hσ m) (hbmin m)
    exact hh.2.1.trans (le_max_left _ _)
  have hbσ (m) : energy (σ m)≤E := by
    have hh := (P.reg n (ζ m) (hζ m)).sublevel_bounds C (ρ m) (σ m) (hρ m) (hσ m) (hbmin m)
    exact hh.2.2.1.trans (le_max_right _ _)
  obtain ⟨f,hf,hlim1,hlim2⟩ := P.minimum_thermal_subsequence hζ hzlim h4ρ h4σ hmin hbρ hbσ
  have he := P.entropyPart_tendsto (fun m => hρ (f m)) (fun m => hσ (f m))
    (fun m => hbρ (f m)) (fun m => hbσ (f m)) hlim1 hlim2
  have hu : Tendsto (fun m => P.entropyPart ρw σw+P.penalty ρw σw+
      ζ (f m)*(numberMoment 4 ρw+numberMoment 4 σw)) atTop
      (𝓝 (P.entropyPart ρw σw+P.penalty ρw σw)) := by
    simpa only [zero_mul,add_zero,Function.comp_apply] using
      ((hzlim.comp hf.tendsto_atTop).mul_const (numberMoment 4 ρw+numberMoment 4 σw)).const_add
        (P.entropyPart ρw σw+P.penalty ρw σw)
  apply le_of_tendsto_of_tendsto he hu
  filter_upwards [] with m
  have hp := P.penalty_nonneg (hρ (f m)) (hσ (f m))
  have hm := mul_nonneg (hζ (f m)).le
    (add_nonneg (numberMoment_nonneg 4 (ρ (f m))) (numberMoment_nonneg 4 (σ (f m))))
  have h1 := P.objective_offset (ζ (f m)) (hζ (f m)) (ρ (f m)) (σ (f m))
  have h2 := P.objective_offset (ζ (f m)) (hζ (f m)) ρw σw
  linarith [hminw (f m)]
end ThermalSetup
end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.ThermalSetup
open scoped BigOperators ComplexConjugate Topology
open QuantumTrace ThermalMetric Filter


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.ThermalSetup.base_nonnegative := @_root_.OAI.EntropyPhotonNumber.ThermalSetup.base_nonnegative
