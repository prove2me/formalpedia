-- Prove2me | solution 2 for OAI.EntropyPhotonNumber.entropy_photon_number_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:53:26.092106+00:00
-- url     : https://prove2.me/submissions/7748be19-906d-40d8-9375-8ddef8c9d650

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Inequality.lean:L692-L705
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.EntropyPhotonNumber.entropy_photon_number_inequality.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_EntropyPhotonNumber_entropy_photon_number_inequality) verbatim and is proved by it.
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Inequality
import Theorems.Thm_OAI_EntropyPhotonNumber_ThermalSetup_base_nonnegative
import Theorems.Thm_OAI_EntropyPhotonNumber_regularizedOutput_energy_bound
import Theorems.Thm_OAI_QuantumTrace_cfc_apply_eigenvector
import Theorems.Thm_OAI_QuantumTrace_double_compression_norm_le
import Theorems.Thm_OAI_QuantumTrace_entropy_small_mass_bound
import Theorems.Thm_OAI_QuantumTrace_entropy_summable_and_le_crossEntropy
import Theorems.Thm_OAI_QuantumTrace_exists_positive_eigenbasis
import Theorems.Thm_OAI_QuantumTrace_tendsto_tsum_of_uniform_tail

-- ---- from OAI.MathematicalPhysics.Fock.Beam ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial

namespace FischerBeam
variable {J : Type*} [Fintype J] [DecidableEq J]

end FischerBeam

namespace FischerBeam

end FischerBeam

namespace FischerBeam

end FischerBeam

namespace FischerBeam

end FischerBeam

end

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

namespace BlockUnitary

variable {S : Type*} {I : S → Type*} [∀ s, Fintype (I s)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable [CompleteSpace E]

end BlockUnitary

namespace BlockUnitary
variable {S : Type*} {I : S → Type*} [∀ s, Fintype (I s)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end BlockUnitary

namespace EntropyPhotonNumber
open FischerBeam

end EntropyPhotonNumber

namespace EntropyPhotonNumber
open FischerBeam

end EntropyPhotonNumber

namespace FischerBeam
open MvPolynomial

end FischerBeam

namespace EntropyPhotonNumber
open FischerBeam

end EntropyPhotonNumber

namespace EntropyPhotonNumber
open FischerBeam
variable {n : ℕ}

theorem beamCoefficient_sector_zero (η : ℝ) (S T : NumberIndex n)
    (k : ∀ j, Fin (S j+1)) (a : ∀ j, Fin (T j+1)) (h : S ≠ T) :
    beamCoefficient η (fun j => k j) (fun j => S j-k j)
      (fun j => a j) (fun j => T j-a j)=0 := by
  classical
  obtain ⟨j,hj⟩ := Function.ne_iff.mp h
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply ite_eq_right
  change ¬ ((k j:ℕ)+(S j-k j)=(a j:ℕ)+(T j-a j))
  have hk := (k j).isLt
  have ha := (a j).isLt
  omega

theorem beamUnitary_apply_sector (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (T : NumberIndex n) (a : ∀ j, Fin (T j+1)) :
    beamUnitary η hη (jointSectorBasis n ⟨T,a⟩)=
      BlockUnitary.rotated (jointSectorBasis n)
        (fun T k a => multiSectorMatrix (Real.sqrt η) (Real.sqrt (1-η)) T k a) ⟨T,a⟩ := by
  exact BlockUnitary.unitary_apply_basis (jointSectorBasis n)
    (fun T k a => multiSectorMatrix (Real.sqrt η) (Real.sqrt (1-η)) T k a) _ _ _

theorem beam_coordinate_sector (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (S T : NumberIndex n) (k : ∀ j, Fin (S j+1)) (a : ∀ j, Fin (T j+1)) :
    inner ℂ (jointSectorBasis n ⟨S,k⟩) (beamUnitary η hη (jointSectorBasis n ⟨T,a⟩)) =
      (beamCoefficient η (fun j => k j) (fun j => S j-k j)
        (fun j => a j) (fun j => T j-a j) : ℂ) := by
  rw [beamUnitary_apply_sector]
  by_cases h : S=T
  · subst T
    erw [BlockUnitary.inner_basis_rotated_same, beam_sectorCoefficient]
  · erw [BlockUnitary.inner_basis_rotated_ne _ _ h,
      beamCoefficient_sector_zero η S T k a h, Complex.ofReal_zero]

theorem beam_coordinate (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (k e a b : NumberIndex n) :
    beamUnitary η hη (lp.single 2 (a,b) 1) (k,e)=(beamCoefficient η k e a b : ℂ) := by
  have hh := beam_coordinate_sector η hη (fun j => k j+e j) (fun j => a j+b j)
    (fun j => (⟨k j, by omega⟩ : Fin (k j+e j+1)))
    (fun j => (⟨a j, by omega⟩ : Fin (a j+b j+1)))
  simp only [jointSectorBasis_apply, sectorEquiv, Nat.add_sub_cancel_left, Equiv.coe_fn_mk] at hh
  simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using hh
end EntropyPhotonNumber

end

end

end OAI

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

theorem entropy_nonneg (b : HilbertBasis ι ℂ E) {T : E →L[ℂ] E} (hp : T.IsPositive)
    (ht : HasSum (fun k => (inner ℂ (b k) (T (b k))).re) 1) :
    0 ≤ ∑' k, (inner ℂ (b k) (entropyOperator T (b k))).re := by
  exact tsum_nonneg (fun k =>
    (entropyOperator_positive hp (norm_le_trace b hp ht)).re_inner_nonneg_right (b k))

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

theorem output_unique {n : ℕ} {η : ℝ} {ρA ρB ρC ρD : State n}
    (hC : IsBeamSplitterOutput η ρA ρB ρC) (hD : IsBeamSplitterOutput η ρA ρB ρD) :
    ρC = ρD := by
  apply state_ext
  exact entry_ext fun k l => (hC k l).unique (hD k l)

theorem output_eq {n : ℕ} {η : ℝ} (hη : η ∈ Set.Icc 0 1) {ρA ρB ρC : State n}
    (hC : IsBeamSplitterOutput η ρA ρB ρC) : ρC = beamOutput η hη ρA ρB :=
  output_unique hC (beamOutput_spec η hη ρA ρB)

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

theorem entropy_nonneg {n : ℕ} (ρ : State n) : 0 ≤ entropy ρ := by
  rw [entropy_eq_quantumTrace]
  exact QuantumTrace.entropy_nonneg (numberBasis n) ρ.positive (trace_one_numberBasis ρ)

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

theorem beamOutput_energy_bound {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    energy (beamOutput η hη ρ σ) ≤ energy ρ + energy σ := by
  have h := beamOutput_energy_le η hη ρ σ
  rw [energyMoment_ofReal (beamOutput_finiteEnergy η hη hρ hσ),
    energyMoment_ofReal hρ, energyMoment_ofReal hσ,
    ← ENNReal.ofReal_add (energy_nonneg ρ) (energy_nonneg σ)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (energy_nonneg ρ) (energy_nonneg σ))).mp h

theorem regularizedOutput_finiteEnergy {n : ℕ} (η δ κ : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hδ : δ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1) {τD τ0 ρ σ : State n}
    (hD : FiniteEnergy τD) (h0 : FiniteEnergy τ0) (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    FiniteEnergy (regularizedOutput η δ κ hη hδ hκ τD τ0 ρ σ) :=
  mixture_finiteEnergy _ _ (beamOutput_finiteEnergy _ _ (beamOutput_finiteEnergy _ _ hρ hσ) hD) h0

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
end

end WeightedGenerator

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ}

end

open QuantumTrace Annihilation WeightedGenerator
variable {n : ℕ}

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber.Regularization
open QuantumTrace Annihilation
variable {n : ℕ} (R : Regularization n)

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

-- ---- from OAI.InformationTheory.PhotonNumber.Inequality ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate Topology
open Filter

namespace HilbertBasis
open scoped _root_.HilbertBasis
variable {I E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem tendsto_isometries (b : HilbertBasis I ℂ E) {l : Filter A}
    (U : A → E ≃ₗᵢ[ℂ] E) (V : E ≃ₗᵢ[ℂ] E)
    (hb : ∀ i, Tendsto (fun a => U a (b i)) l (𝓝 (V (b i)))) (x : E) :
    Tendsto (fun a => U a x) l (𝓝 (V x)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨s,hs⟩ := ((b.hasSum_repr x).eventually
    (Metric.ball_mem_nhds x (by positivity : 0<ε/3))).exists
  let v := ∑ i ∈ s, (b.repr x i) • b i
  have hdist : dist v x<ε/3 := hs
  have hv : Tendsto (fun a => U a v) l (𝓝 (V v)) := by
    simp only [v,map_sum,map_smul]
    exact tendsto_finsetSum s (fun i _ => (hb i).const_smul _)
  filter_upwards [hv.eventually (Metric.ball_mem_nhds (V v) (by positivity : 0<ε/3))] with a ha
  have h1 := dist_triangle (U a x) (U a v) (V x)
  have h2 := dist_triangle (U a v) (V v) (V x)
  have h3 : dist (U a v) (V v)<ε/3 := ha
  rw [(U a).dist_map] at h1
  rw [V.dist_map] at h2
  rw [dist_comm v x] at hdist
  linarith
end HilbertBasis

namespace EntropyPhotonNumber
open QuantumTrace TensorLp

theorem continuous_oneModeBeamCoefficient (k e a b : ℕ) :
    Continuous (fun η => oneModeBeamCoefficient η k e a b) := by
  unfold oneModeBeamCoefficient
  split_ifs
  · apply continuous_const.mul
    apply continuous_finsetSum
    intro p _hp
    apply continuous_finsetSum
    intro q _hq
    split_ifs <;> fun_prop
  · exact continuous_const

theorem continuous_beamCoefficient {n : ℕ} (k e a b : NumberIndex n) :
    Continuous (fun η => beamCoefficient η k e a b) := by
  exact continuous_finsetProd _ (fun j _ => continuous_oneModeBeamCoefficient _ _ _ _)

theorem tendsto_beamUnitary {n : ℕ} {A : Type*} {l : Filter A} {η : A → ℝ}
    (hη : ∀ a, η a∈Set.Icc 0 1) {θ : ℝ} (hθ : θ∈Set.Icc 0 1)
    (hlim : Tendsto η l (𝓝 θ)) (x : JointFock n) :
    Tendsto (fun a => beamUnitary (η a) (hη a) x) l (𝓝 (beamUnitary θ hθ x)) := by
  apply _root_.OAI.HilbertBasis.tendsto_isometries (jointSectorBasis n)
    (fun a => beamUnitary (η a) (hη a)) (beamUnitary θ hθ)
  rintro ⟨T,i⟩
  simp only [beamUnitary_apply_sector,BlockUnitary.rotated,← beam_sectorCoefficient]
  refine tendsto_finsetSum _ (fun k _ => ?_)
  exact (Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((continuous_beamCoefficient _ _ _ _).continuousAt.tendsto.comp hlim)).smul_const _

theorem tendsto_beamOutput_parameter {n : ℕ} {A : Type*} {l : Filter A} {η : A → ℝ}
    (hη : ∀ a, η a∈Set.Icc 0 1) {θ : ℝ} (hθ : θ∈Set.Icc 0 1)
    (hlim : Tendsto η l (𝓝 θ)) (ρ σ : State n) :
    Tendsto (fun a => (beamOutput (η a) (hη a) ρ σ).op) l (𝓝 (beamOutput θ hθ ρ σ).op) := by
  apply TraceEnsemble.tendsto_operator
    (fun a => hasSum_slice_family (mixedVector_norm (η a) (hη a) ρ σ))
    (hasSum_slice_family (mixedVector_norm θ hθ ρ σ))
  intro bi
  exact (sliceCLM bi.1).continuous.tendsto _ |>.comp
    (tendsto_beamUnitary hη hθ hlim (tensor (rootColumn ρ bi.2.1) (rootColumn σ bi.2.2)))

end EntropyPhotonNumber

end

namespace EntropyPhotonNumber
open scoped BigOperators Topology

open Set Filter ThermalMetric

theorem h_antitone {a b : ℝ} (ha : 0<a) (hab : a ≤ b) : h b ≤ h a := by
  have hb := lt_of_lt_of_le ha hab
  unfold h
  rw [← Real.log_div (by linarith : b+1≠0) hb.ne',← Real.log_div (by linarith : a+1≠0) ha.ne']
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ hb ha).mpr
  nlinarith

theorem g_ge_log {t : ℝ} (ht : 0<t) : Real.log (t+1) ≤ g t := by
  have hp := mul_nonneg ht.le (h_pos ht).le
  dsimp [g,h] at *
  nlinarith

theorem g_surjective_nonneg {s : ℝ} (hs : 0  ≤  s) : ∃ t : ℝ, 0 ≤ t ∧ g t=s := by
  have hb : s ≤ g (Real.exp s) := by
    calc
      s = Real.log (Real.exp s) := (Real.log_exp s).symm
      _  ≤  Real.log (Real.exp s+1) := Real.log_le_log (Real.exp_pos s) (by linarith)
      _  ≤  g (Real.exp s) := g_ge_log (Real.exp_pos s)
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (Real.exp_pos s).le continuous_g.continuousOn
    (show s∈Set.Icc (g 0) (g (Real.exp s)) from ⟨by simpa using hs,hb⟩)
  exact ⟨t,ht.1,he⟩

theorem gInv_nonneg {s : ℝ} (hs : 0  ≤  s) : 0 ≤ gInv s := by
  obtain ⟨t,ht,rfl⟩ := g_surjective_nonneg hs
  simpa only [gInv_g ht] using ht

theorem g_gInv {s : ℝ} (hs : 0  ≤  s) : g (gInv s)=s := by
  obtain ⟨t,ht,rfl⟩ := g_surjective_nonneg hs
  rw [gInv_g ht]

theorem le_gInv_iff {t s : ℝ} (ht : 0 ≤ t) (hs : 0  ≤  s) : t ≤ gInv s ↔ g t ≤ s := by
  have hh := strictMonoOn_g.le_iff_le ht (gInv_nonneg hs)
  rw [g_gInv hs] at hh
  exact hh.symm

end EntropyPhotonNumber

open scoped BigOperators ComplexConjugate Topology

namespace EntropyPhotonNumber

section
open QuantumTrace ThermalMetric Filter

namespace ThermalInterior
variable (T : ThermalInterior)
theorem eps_limit : Tendsto T.eps atTop (𝓝 0) := by
  change Tendsto (fun m : ℕ => min T.cap (1/((m:ℝ)+1))) atTop (𝓝 (0:ℝ))
  simpa only [min_eq_right T.cap_pos.le,eps] using
    (tendsto_const_nhds.min tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun m : ℕ => min T.cap (1/((m:ℝ)+1))) atTop (𝓝 (min T.cap 0)))
theorem kap_limit : Tendsto T.kap atTop (𝓝 0) := by
  apply squeeze_zero (fun m => (T.kap_pos m).le) (fun _ => min_le_left _ _)
  have hh : Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcomp := hh.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun m : ℕ => 1/(((m+1:ℕ):ℝ)+1)) atTop (𝓝 (0:ℝ)) at hcomp
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hcomp

theorem out_limit {n : ℕ} (ρ σ : State n) :
    Tendsto (fun m => ((T.setup m).out ρ σ).op) atTop (𝓝 (T.raw ρ σ).op) := by
  have hc : Tendsto (fun m => (T.kap m : ℂ)) atTop (𝓝 0) := by
    simpa using T.kap_limit.ofReal
  have h1 := (hc.const_sub 1).smul_const (T.raw ρ σ).op
  have h2 := hc.zero_smul_const (thermalState n T.r0 T.r0_pos).op
  have hh := h1.add h2
  simpa only [sub_zero,one_smul,add_zero,
    ThermalSetup.out,ThermalSetup.output_op,setup,ThermalSetup.raw,ThermalSetup.middle,
    ThermalSetup.r0,raw,r0,a,Complex.ofReal_sub,Complex.ofReal_one,Function.comp_apply] using hh

theorem out_entropy_limit {n : ℕ} {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    Tendsto (fun m => entropy ((T.setup m).out ρ σ)) atTop (𝓝 (entropy (T.raw ρ σ))) := by
  let E := energy ρ+energy σ+energy (thermalState n T.d T.hd)+energy (thermalState n T.r0 T.r0_pos)
  apply tendsto_entropy (E:=E)
  · intro m
    exact regularizedOutput_finiteEnergy T.η (1-T.θ) (T.kap m)
      (T.setup m).η_mem (T.setup m).δ_mem (T.setup m).κ_mem
      (thermalState_finiteEnergy n T.d T.hd) (thermalState_finiteEnergy n T.r0 T.r0_pos) hρ hσ
  · exact beamOutput_finiteEnergy _ _ (beamOutput_finiteEnergy _ _ hρ hσ)
      (thermalState_finiteEnergy n T.d T.hd)
  · intro m
    exact regularizedOutput_energy_bound T.η (1-T.θ) (T.kap m)
      (T.setup m).η_mem (T.setup m).δ_mem (T.setup m).κ_mem
      (thermalState_finiteEnergy n T.d T.hd) (thermalState_finiteEnergy n T.r0 T.r0_pos) hρ hσ
  · have hh := beamOutput_energy_bound T.θ ⟨T.hθ.1.le,T.hθ.2.le⟩
      (beamOutput_finiteEnergy T.η ⟨T.hη.1.le,T.hη.2.le⟩ hρ hσ) (thermalState_finiteEnergy n T.d T.hd)
    have hi := beamOutput_energy_bound T.η ⟨T.hη.1.le,T.hη.2.le⟩ hρ hσ
    have hp := energy_nonneg (thermalState n T.r0 T.r0_pos)
    dsimp [E,raw]
    linarith
  · exact T.out_limit ρ σ

theorem entropy_tangent {n : ℕ} {ρ σ : State n} (hρ : FiniteMoment 4 ρ) (hσ : FiniteMoment 4 σ) :
    0≤(entropy (T.raw ρ σ)-n*g T.r0)/h T.r0-
      (T.θ*T.η)*(entropy ρ-n*g T.r1)/h T.r1-
      (T.θ*(1-T.η))*(entropy σ-n*g T.r2)/h T.r2 := by
  have ho := T.out_entropy_limit (finiteMoment_finiteEnergy (by decide : 1≤4) hρ)
    (finiteMoment_finiteEnergy (by decide : 1≤4) hσ)
  have hw1 := ((T.kap_limit.const_sub 1).mul_const T.θ).mul_const T.η
  have hw2 := ((T.kap_limit.const_sub 1).mul_const T.θ).mul_const (1-T.η)
  have he := (((ho.sub_const (n*g T.r0)).div_const (h T.r0)).sub
    ((hw1.mul_const (entropy ρ-n*g T.r1)).div_const (h T.r1))).sub
    ((hw2.mul_const (entropy σ-n*g T.r2)).div_const (h T.r2))
  have hp := T.eps_limit.mul
    (((hw1.div_const (h T.r1)).mul_const (thermalRelative T.r1 ρ)).add
      ((hw2.div_const (h T.r2)).mul_const (thermalRelative T.r2 σ)))
  have hh := he.add hp
  simp only [sub_zero,one_mul,zero_mul,add_zero] at hh
  apply ge_of_tendsto hh
  filter_upwards [] with m
  exact (T.setup m).base_nonnegative hρ hσ
end ThermalInterior
end

section
open QuantumTrace FischerBeam TensorLp MvPolynomial

theorem oneModeBeamCoefficient_one (k e a b : ℕ) :
    oneModeBeamCoefficient 1 k e a b=if k=a ∧ e=b then 1 else 0 := by
  classical
  rw [oneModeBeamCoefficient_eq]
  have hp : rotated 1 0 a b=monomial (degree a b) 1 := by
    simp only [rotated,creatorA,creatorB,one_smul,zero_smul,sub_zero,zero_add,
      X_pow_eq_monomial,monomial_mul,one_mul,degree]
  simp only [Real.sqrt_one,sub_self,Real.sqrt_zero,hp,coeff_monomial,degree_eq_iff,eq_comm (a := a) (b := k),eq_comm (a := b) (b := e)]
  split_ifs with hh
  · rcases hh with ⟨rfl,rfl⟩
    rw [div_self (Real.sqrt_ne_zero'.mpr (by simp [weight_degree]; positivity)),mul_one]
  · simp

theorem beamCoefficient_one {n : ℕ} (k e a b : NumberIndex n) :
    beamCoefficient 1 k e a b=if k=a ∧ e=b then 1 else 0 := by
  classical
  simp only [beamCoefficient,oneModeBeamCoefficient_one]
  by_cases hh : k=a ∧ e=b
  · rcases hh with ⟨rfl,rfl⟩; simp
  · rw [ite_eq_right hh]
    have hj : ∃ j, ¬ (k j=a j ∧ e j=b j) := by
      by_contra hn
      push Not at hn
      exact hh ⟨funext (fun j => (hn j).1),funext (fun j => (hn j).2)⟩
    obtain ⟨j,hj⟩ := hj
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

theorem beamUnitary_one {n : ℕ} (h1 : (1:ℝ)∈Set.Icc 0 1) (x : JointFock n) :
    beamUnitary 1 h1 x=x := by
  have he : (beamUnitary (n:=n) 1 h1).toContinuousLinearEquiv.toContinuousLinearMap=ContinuousLinearMap.id ℂ (JointFock n) := by
    apply ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr (jointNumberBasis n).dense_span)
    rintro _ ⟨⟨a,b⟩,rfl⟩
    apply lp.ext
    funext ⟨k,e⟩
    simp only [jointNumberBasis_apply]
    change beamUnitary 1 h1 (lp.single 2 (a,b) 1 : JointFock n) (k,e)=
      (lp.single 2 (a,b) 1 : JointFock n) (k,e)
    simp only [beam_coordinate,beamCoefficient_one,lp.single_apply]
    split_ifs <;> simp_all [eq_comm]
  exact congrArg (fun A : JointFock n →L[ℂ] JointFock n => A x) he

theorem beamOutput_one {n : ℕ} (h1 : (1:ℝ)∈Set.Icc 0 1) (ρ σ : State n) :
    beamOutput 1 h1 ρ σ=ρ := by
  apply State.ext_op
  apply entry_ext
  intro k l
  have hv := (TraceEnsemble.hasSum_tensor_norm (rootColumn_norm ρ) (rootColumn_norm σ)).summable
  have hh := partialTrace_entry hv k l
  simp only [TraceEnsemble.tensor_entry (rootColumn_norm ρ).summable (rootColumn_norm σ).summable,
    rootColumn_operator] at hh
  have hs : HasSum (fun e => entry σ.op e e) (1:ℂ) := by
    convert! σ.trace_one.mapL Complex.ofRealCLM using 1
    funext e
    apply Complex.ext
    · rfl
    · exact (RCLike.nonneg_iff.mp (σ.positive.inner_nonneg_right (numberKet e))).2
  have ht := hs.mul_left (entry ρ.op k l)
  rw [mul_one] at ht
  have he := hh.unique ht
  change entry (partialTrace (mixedVector 1 h1 ρ σ)) k l=entry ρ.op k l
  have hm : mixedVector 1 h1 ρ σ=(fun ij => tensor (rootColumn ρ ij.1) (rootColumn σ ij.2)) := by
    funext ij
    exact beamUnitary_one h1 _
  rw [hm]
  exact he
end

section
open QuantumTrace ThermalMetric Filter

theorem continuousAt_h_pos {r : ℝ} (hr : 0<r) : ContinuousAt h r := by
  change ContinuousAt (fun x : ℝ => Real.log (x+1)-Real.log x) r
  have hs : ContinuousAt (fun x : ℝ => x+1) r := continuousAt_id.add continuousAt_const
  apply ContinuousAt.sub
  · exact hs.log (by linarith : r+1≠0)
  · exact Real.continuousAt_log hr.ne'

theorem tendsto_entropy_beamOutput_parameter {n : ℕ} {A : Type*} {l : Filter A} {η : A → ℝ}
    (hη : ∀ a, η a∈Set.Icc 0 1) {θ : ℝ} (hθ : θ∈Set.Icc 0 1)
    (hlim : Tendsto η l (𝓝 θ)) {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    Tendsto (fun a => entropy (beamOutput (η a) (hη a) ρ σ)) l
      (𝓝 (entropy (beamOutput θ hθ ρ σ))) := by
  exact tendsto_entropy (E:=energy ρ+energy σ)
    (fun a => beamOutput_finiteEnergy (η a) (hη a) hρ hσ)
    (beamOutput_finiteEnergy θ hθ hρ hσ)
    (fun a => beamOutput_energy_bound (η a) (hη a) hρ hσ)
    (beamOutput_energy_bound θ hθ hρ hσ)
    (tendsto_beamOutput_parameter hη hθ hlim ρ σ)

theorem interiorTransmission_mem (m : ℕ) : interiorTransmission m∈Set.Ioo 0 1 := by
  have h1 : 0<1/((m:ℝ)+2) := by positivity
  have h2 : 1/((m:ℝ)+2)<1 := (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) m])
  exact ⟨sub_pos.mpr h2,sub_lt_self _ h1⟩
theorem interiorTransmission_limit : Tendsto interiorTransmission atTop (𝓝 1) := by
  have hh : Tendsto (fun m : ℕ => 1/((m:ℝ)+2)) atTop (𝓝 (0:ℝ)) := by
    have hf : Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc := hf.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun m : ℕ => 1/(((m+1:ℕ):ℝ)+1)) atTop (𝓝 (0:ℝ)) at hc
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hc
  change Tendsto (fun m : ℕ => 1-1/((m:ℝ)+2)) atTop (𝓝 (1:ℝ))
  simpa only [sub_zero] using hh.const_sub 1

theorem entropy_tangent_beam {n : ℕ} {η r1 r2 : ℝ} (hη : η∈Set.Ioo 0 1)
    (hr1 : 0<r1) (hr2 : 0<r2) {ρ σ : State n} (hρ : FiniteMoment 4 ρ) (hσ : FiniteMoment 4 σ) :
    0≤(entropy (beamOutput η ⟨hη.1.le,hη.2.le⟩ ρ σ)-n*g (η*r1+(1-η)*r2))/h (η*r1+(1-η)*r2)-
      η*(entropy ρ-n*g r1)/h r1-(1-η)*(entropy σ-n*g r2)/h r2 := by
  let T : ℕ → ThermalInterior := fun m => {
    η := η, θ := interiorTransmission m, d := 1, r1 := r1, r2 := r2,
    hη := hη, hθ := interiorTransmission_mem m, hd := zero_lt_one, hr1 := hr1, hr2 := hr2 }
  have hEρ := finiteMoment_finiteEnergy (by decide : 1≤4) hρ
  have hEσ := finiteMoment_finiteEnergy (by decide : 1≤4) hσ
  have hl := tendsto_entropy_beamOutput_parameter
    (fun m => ⟨(interiorTransmission_mem m).1.le,(interiorTransmission_mem m).2.le⟩)
    (show (1:ℝ)∈Set.Icc 0 1 from ⟨zero_le_one,le_rfl⟩) interiorTransmission_limit
    (beamOutput_finiteEnergy η ⟨hη.1.le,hη.2.le⟩ hEρ hEσ) (thermalState_finiteEnergy n 1 zero_lt_one)
  rw [beamOutput_one] at hl
  have hr0 : 0<η*r1+(1-η)*r2 := add_pos (mul_pos hη.1 hr1) (mul_pos (sub_pos.mpr hη.2) hr2)
  have hrlim : Tendsto (fun m => (T m).r0) atTop (𝓝 (η*r1+(1-η)*r2)) := by
    have hh := (interiorTransmission_limit.mul_const (η*r1+(1-η)*r2)).add
      ((interiorTransmission_limit.const_sub 1).mul_const 1)
    simpa only [one_mul,sub_self,zero_mul,add_zero,T,ThermalInterior.r0,ThermalInterior.a] using hh
  have hg := continuous_g.continuousAt.tendsto.comp hrlim
  have hh := (continuousAt_h_pos hr0).tendsto.comp hrlim
  have hmain := ((hl.sub (hg.const_mul (n:ℝ))).div hh (h_pos hr0).ne').sub
    ((interiorTransmission_limit.mul_const η).mul_const (entropy ρ-n*g r1) |>.div_const (h r1))
  have hmain' := hmain.sub
    ((interiorTransmission_limit.mul_const (1-η)).mul_const (entropy σ-n*g r2) |>.div_const (h r2))
  simp only [one_mul] at hmain'
  apply ge_of_tendsto hmain'
  filter_upwards [] with m
  exact (T m).entropy_tangent hρ hσ
end

namespace NumberCutoff
open QuantumTrace Filter InnerProductSpace

variable {n : ℕ} (ρ : State n) (F : Finset (NumberIndex n))
theorem diagonal (k : NumberIndex n) :
    (entry (state ρ F).op k k).re=
      (if k∈F then (entry ρ.op k k).re else 0)+(if k=0 then 1-mass ρ F else 0) := by
  classical
  change (entry (compressed ρ F+((1-mass ρ F:ℝ):ℂ) • vacuum) k k).re=_
  simp only [entry,add_apply,smul_apply,inner_add_right,inner_smul_right]
  change (entry (compressed ρ F) k k+((1-mass ρ F:ℝ):ℂ)*entry vacuum k k).re=_
  rw [compressed_diagonal,vacuum_diagonal]
  split_ifs <;> simp [entry]

theorem finiteMoment (m : ℕ) : FiniteMoment m (state ρ F) := by
  classical
  apply summable_of_ne_finset_zero (s:=insert 0 F)
  intro k hk
  have hF : k∉F := fun h => hk (Finset.mem_insert_of_mem h)
  have h0 : k≠0 := by intro h; subst k; exact hk (Finset.mem_insert_self 0 F)
  rw [diagonal,ite_eq_right hF,ite_eq_right h0]
  simp

theorem energy_le (hρ : FiniteEnergy ρ) : energy (state ρ F)≤energy ρ := by
  classical
  have he (k : NumberIndex n) : (totalNumber k:ℝ)*(entry (state ρ F).op k k).re=
      if k∈F then (totalNumber k:ℝ)*(entry ρ.op k k).re else 0 := by
    rw [diagonal]
    by_cases h0 : k=0
    · subst k; simp [totalNumber]
    · rw [ite_eq_right h0,add_zero]; split_ifs <;> simp [entry]
  unfold energy
  simp only [he]
  have hs : HasSum (fun k => if k∈F then (totalNumber k:ℝ)*(entry ρ.op k k).re else 0)
      (∑ k∈F, (totalNumber k:ℝ)*(entry ρ.op k k).re) := by
    simpa only [Finset.sum_ite_mem, Finset.inter_self] using
      (hasSum_sum_of_ne_finset_zero (s:=F)
        (f:=fun k => if k∈F then (totalNumber k:ℝ)*(entry ρ.op k k).re else 0)
        (by intro k hk; simp only [ite_eq_right hk]))
  rw [hs.tsum_eq]
  exact hρ.sum_le_tsum F (fun k _ => mul_nonneg (Nat.cast_nonneg _)
    (ρ.positive.re_inner_nonneg_right (numberKet k)))

theorem limit : Tendsto (fun F : Finset (NumberIndex n) => (state ρ F).op) atTop (𝓝 ρ.op) := by
  have hm : Tendsto (mass ρ) atTop (𝓝 1) := ρ.trace_one
  have hc : Tendsto (compressed ρ) atTop (𝓝 ρ.op) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun F => (norm_sub_rev _ _).le.trans (double_compression_norm_le (numberBasis n) ρ.positive
        (trace_one_numberBasis ρ) F))
    have hh := (Real.continuous_sqrt.continuousAt.tendsto.comp (hm.const_sub 1)).const_mul 2
    simpa only [sub_self,Real.sqrt_zero,mul_zero,numberBasis_apply,entry,projection,compressed,mass,Function.comp_apply] using hh
  have hr : Tendsto (fun F => ((1 - mass ρ F : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa using (hm.const_sub 1).ofReal
  have hh := hc.add (hr.zero_smul_const (vacuum (n:=n)))
  simpa only [add_zero,state] using hh
end NumberCutoff

open QuantumTrace ThermalMetric Filter

theorem entropy_tangent_finiteEnergy {n : ℕ} {η r1 r2 : ℝ} (hη : η∈Set.Ioo 0 1)
    (hr1 : 0<r1) (hr2 : 0<r2) {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    0≤(entropy (beamOutput η ⟨hη.1.le,hη.2.le⟩ ρ σ)-n*g (η*r1+(1-η)*r2))/h (η*r1+(1-η)*r2)-
      η*(entropy ρ-n*g r1)/h r1-(1-η)*(entropy σ-n*g r2)/h r2 := by
  let ρm := NumberCutoff.state ρ
  let σm := NumberCutoff.state σ
  have hρm (F : Finset (NumberIndex n)) : FiniteEnergy (ρm F) :=
    finiteMoment_finiteEnergy (by decide : 1≤4) (NumberCutoff.finiteMoment ρ F 4)
  have hσm (F : Finset (NumberIndex n)) : FiniteEnergy (σm F) :=
    finiteMoment_finiteEnergy (by decide : 1≤4) (NumberCutoff.finiteMoment σ F 4)
  have hρlim := tendsto_entropy hρm hρ (fun F => NumberCutoff.energy_le ρ F hρ) le_rfl (NumberCutoff.limit ρ)
  have hσlim := tendsto_entropy hσm hσ (fun F => NumberCutoff.energy_le σ F hσ) le_rfl (NumberCutoff.limit σ)
  have hclim := tendsto_entropy (E:=energy ρ+energy σ)
    (fun F => beamOutput_finiteEnergy η ⟨hη.1.le,hη.2.le⟩ (hρm F) (hσm F))
    (beamOutput_finiteEnergy η ⟨hη.1.le,hη.2.le⟩ hρ hσ)
    (fun F => (beamOutput_energy_bound η ⟨hη.1.le,hη.2.le⟩ (hρm F) (hσm F)).trans
      (add_le_add (NumberCutoff.energy_le ρ F hρ) (NumberCutoff.energy_le σ F hσ)))
    (beamOutput_energy_bound η ⟨hη.1.le,hη.2.le⟩ hρ hσ)
    (tendsto_beamOutput η ⟨hη.1.le,hη.2.le⟩ (NumberCutoff.limit ρ) (NumberCutoff.limit σ))
  have hl := (((hclim.sub_const ((n:ℝ)*g (η*r1+(1-η)*r2))).div_const (h (η*r1+(1-η)*r2))).sub
    (((hρlim.sub_const ((n:ℝ)*g r1)).const_mul η).div_const (h r1)))
  have hl' := hl.sub (((hσlim.sub_const ((n:ℝ)*g r2)).const_mul (1-η)).div_const (h r2))
  apply ge_of_tendsto hl'
  filter_upwards [] with F
  exact entropy_tangent_beam hη hr1 hr2 (NumberCutoff.finiteMoment ρ F 4) (NumberCutoff.finiteMoment σ F 4)

theorem positiveReference_pos {a : ℝ} (ha : 0≤a) (m : ℕ) : 0<positiveReference a m := by
  unfold positiveReference
  positivity
theorem positiveReference_le {a : ℝ} (_ha : 0≤a) (m : ℕ) : positiveReference a m≤a+1 := by
  unfold positiveReference
  have hm : 0<(m:ℝ)+1 := by positivity
  have hdiv : 1/((m:ℝ)+1)≤1 := (div_le_one hm).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) m])
  linarith [hdiv]
theorem positiveReference_limit (a : ℝ) : Tendsto (positiveReference a) atTop (𝓝 a) := by
  have hh := (tendsto_one_div_add_atTop_nhds_zero_nat :
    Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 (0:ℝ))).const_add a
  change Tendsto (fun m : ℕ => a+1/((m:ℝ)+1)) atTop (𝓝 a)
  simpa only [add_zero] using hh

theorem reference_error_limit {a : ℝ} (ha : 0≤a) :
    Tendsto (fun m => (g a-g (positiveReference a m))/h (positiveReference a m)) atTop (𝓝 0) := by
  have hc : 0<h (a+1) := h_pos (by linarith)
  have hnum := (continuous_g.continuousAt.tendsto.comp (positiveReference_limit a)).const_sub (g a)
  have hbound := (hnum.norm.div_const (h (a+1)))
  have hnorm : Tendsto (fun m => ‖(g a-g (positiveReference a m))/h (positiveReference a m)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun m => ?_) (by simpa only [sub_self,norm_zero,zero_div] using hbound)
    rw [norm_div,Real.norm_eq_abs (h (positiveReference a m)),abs_of_pos (h_pos (positiveReference_pos ha m))]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hc
      (h_antitone (positiveReference_pos ha m) (positiveReference_le ha m))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using hnorm

theorem epni_entropy_interior {n : ℕ} (hn : 1≤n) {η : ℝ} (hη : η∈Set.Ioo 0 1)
    {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    g (η*gInv (entropy ρ/n)+(1-η)*gInv (entropy σ/n)) ≤
      entropy (beamOutput η ⟨hη.1.le,hη.2.le⟩ ρ σ)/n := by
  have hnR : 0<(n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  let a := gInv (entropy ρ/n)
  let b := gInv (entropy σ/n)
  have ha : 0≤a := gInv_nonneg (div_nonneg (entropy_nonneg ρ) hnR.le)
  have hb : 0≤b := gInv_nonneg (div_nonneg (entropy_nonneg σ) hnR.le)
  have hga : g a=entropy ρ/n := g_gInv (div_nonneg (entropy_nonneg ρ) hnR.le)
  have hgb : g b=entropy σ/n := g_gInv (div_nonneg (entropy_nonneg σ) hnR.le)
  have hρeq : entropy ρ=(n:ℝ)*g a := by rw [hga]; field_simp
  have hσeq : entropy σ=(n:ℝ)*g b := by rw [hgb]; field_simp
  have hc0 : 0≤η*a+(1-η)*b := add_nonneg (mul_nonneg hη.1.le ha) (mul_nonneg (sub_nonneg.mpr hη.2.le) hb)
  rcases eq_or_lt_of_le hc0 with hzero | hpos
  · rw [← hzero,g_zero]
    exact div_nonneg (entropy_nonneg _) hnR.le
  have hrlim := ((positiveReference_limit a).const_mul η).add
    ((positiveReference_limit b).const_mul (1-η))
  have hg := continuous_g.continuousAt.tendsto.comp hrlim
  have hh := (continuousAt_h_pos hpos).tendsto.comp hrlim
  have heρ := (reference_error_limit ha).const_mul ((n:ℝ)*η)
  have heσ := (reference_error_limit hb).const_mul ((n:ℝ)*(1-η))
  have hout := ((hg.const_mul (n:ℝ)).const_sub
    (entropy (beamOutput η ⟨hη.1.le,hη.2.le⟩ ρ σ))).div hh (h_pos hpos).ne'
  have hmain := (hout.sub heρ).sub heσ
  simp only [mul_zero,sub_zero] at hmain
  have hnonneg : 0≤(entropy (beamOutput η ⟨hη.1.le,hη.2.le⟩ ρ σ)-(n:ℝ)*g (η*a+(1-η)*b))/h (η*a+(1-η)*b) := by
    apply ge_of_tendsto hmain
    filter_upwards [] with m
    have ht := entropy_tangent_finiteEnergy hη (positiveReference_pos ha m) (positiveReference_pos hb m) hρ hσ
    rw [hρeq,hσeq] at ht
    convert! ht using 1
    dsimp only [Pi.div_apply,Function.comp_apply]
    ring
  have ht := (le_div_iff₀ (h_pos hpos)).mp hnonneg
  change g (η*a+(1-η)*b)≤_
  exact (le_div_iff₀ hnR).mpr (by nlinarith)

theorem epni_entropy_closed {n : ℕ} (hn : 1 ≤ n) {η : ℝ} (hη : η∈Set.Icc 0 1)
    {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    g (η*gInv (entropy ρ/n)+(1-η)*gInv (entropy σ/n))  ≤ 
      entropy (beamOutput η hη ρ σ)/n := by
  let ηm : ℕ → ℝ := fun m => interiorTransmission m*η+(1-interiorTransmission m)/2
  have hηm (m : ℕ) : ηm m∈Set.Ioo 0 1 := by
    have ht := interiorTransmission_mem m
    have hp := mul_nonneg ht.1.le hη.1
    have hu : interiorTransmission m*η ≤ interiorTransmission m :=
      mul_le_of_le_one_right ht.1.le hη.2
    dsimp [ηm]
    constructor <;> linarith [ht.1,ht.2]
  have hlim : Tendsto ηm atTop (𝓝 η) := by
    have hh := (interiorTransmission_limit.mul_const η).add
      ((interiorTransmission_limit.const_sub 1).div_const 2)
    simpa only [one_mul,sub_self,zero_div,add_zero,ηm] using hh
  have hout := (tendsto_entropy_beamOutput_parameter
    (fun m => ⟨(hηm m).1.le,(hηm m).2.le⟩) hη hlim hρ hσ).div_const (n:ℝ)
  have harg := (hlim.mul_const (gInv (entropy ρ/n))).add
    ((hlim.const_sub 1).mul_const (gInv (entropy σ/n)))
  have hg := continuous_g.continuousAt.tendsto.comp harg
  exact le_of_tendsto_of_tendsto hg hout (Eventually.of_forall (fun m => epni_entropy_interior hn (hηm m) hρ hσ))

theorem entropy_photon_number_inequality
    (n : ℕ) (hn : 1 ≤ n) (ρA ρB ρC : State n)
    (hA : FiniteEnergy ρA) (hB : FiniteEnergy ρB)
    (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hC : IsBeamSplitterOutput η ρA ρB ρC) :
    η * gInv (entropy ρA / n) + (1 - η) * gInv (entropy ρB / n) ≤
      gInv (entropy ρC / n) := by
  have hnR : 0<(n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have ha := gInv_nonneg (div_nonneg (entropy_nonneg ρA) hnR.le)
  have hb := gInv_nonneg (div_nonneg (entropy_nonneg ρB) hnR.le)
  have hw := add_nonneg (mul_nonneg hη.1 ha) (mul_nonneg (sub_nonneg.mpr hη.2) hb)
  apply (le_gInv_iff hw (div_nonneg (entropy_nonneg ρC) hnR.le)).mpr
  rw [output_eq hη hC]
  exact epni_entropy_closed hn hη hA hB
end EntropyPhotonNumber

end

end OAI

-- ---- mission target ----
open OAI OAI.EntropyPhotonNumber
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate Topology
open QuantumTrace ThermalMetric Filter

theorem solution
    (n : ℕ) (hn : 1 ≤ n) (ρA ρB ρC : State n)
    (hA : FiniteEnergy ρA) (hB : FiniteEnergy ρB)
    (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hC : IsBeamSplitterOutput η ρA ρB ρC) :
    η * gInv (entropy ρA / n) + (1 - η) * gInv (entropy ρB / n) ≤
      gInv (entropy ρC / n) := by
  first
    | exact OAI.EntropyPhotonNumber.entropy_photon_number_inequality n hn ρA ρB ρC hA hB η hη hC
    | exact OAI.EntropyPhotonNumber.entropy_photon_number_inequality
    | (apply OAI.EntropyPhotonNumber.entropy_photon_number_inequality <;> assumption)
    | (intros; apply OAI.EntropyPhotonNumber.entropy_photon_number_inequality <;> assumption)
