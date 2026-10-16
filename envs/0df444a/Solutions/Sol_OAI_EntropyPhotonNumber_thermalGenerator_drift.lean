-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.thermalGenerator_drift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:35:33.06917+00:00
-- url     : https://prove2.me/submissions/85ea51b1-57e2-4110-a150-0856f4036082

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean:L244-L275
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.thermalGenerator_drift. The node keeps its source
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
import Theorems.Thm_OAI_Annihilation_diagonal_mode_left

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

theorem gain_lower_sq (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    ‖gain j false x k‖^2 = numberWeight k^4*((k j:ℝ)+1)/numberWeight (up j k)^6 * ‖x (up j k)‖^2 := by
  simp only [gain, Bool.false_eq_true, ↓reduceIte, sandwich_apply, coefficient, norm_mul,
    mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt (show 0≤(k j:ℝ)+1 by positivity)]
  ring

theorem gain_raise_sq (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    ‖gain j true x (up j k)‖^2 = numberWeight (up j k)^4*((k j:ℝ)+1)/numberWeight k^6 * ‖x k‖^2 := by
  simp only [gain, ↓reduceIte, creationSandwich_up, creationCoefficient, norm_mul,
    mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt (show 0≤(k j:ℝ)+1 by positivity)]
  ring

theorem gain_raise_zero (j : Fin n) (x : Fock n) (k : NumberIndex n) (hk : k j=0) :
    gain j true x k=0 := creationSandwich_zero 2 3 (by omega) j x k hk

theorem gain_lower_diagonal (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k /numberWeight k^4| ≤ C) (j : Fin n) (x : Fock n) :
    HasSum (fun k => (k j:ℝ)*f (down j k)/numberWeight k^6 *‖x k‖^2)
      (inner ℂ (gain j false x) (diagonal (fun k => f k/numberWeight k^4) C hC hf (gain j false x))).re := by
  have hh := diagonal_quadratic (fun k => f k/numberWeight k^4) C hC hf (gain j false x)
  have he (k : NumberIndex n) : f k/numberWeight k^4 *‖gain j false x k‖^2 =
      (((up j k) j:ℝ)*f (down j (up j k))/numberWeight (up j k)^6 *‖x (up j k)‖^2) := by
    rw [gain_lower_sq, up_same, down_up, Nat.cast_add, Nat.cast_one]
    have hw : numberWeight k ≠ 0 := by linarith [numberWeight_one_le k]
    field_simp
  have hz (k : NumberIndex n) (hk : k ∉ Set.range (up j)) :
      (k j:ℝ)*f (down j k)/numberWeight k^6 *‖x k‖^2=0 := by
    rcases index_cases j k with he | ⟨l,rfl⟩
    · simp [he]
    · exact (hk ⟨l,rfl⟩).elim
  apply (up_injective j).hasSum_iff hz |>.mp
  convert! hh using 1
  ext k
  exact (he k).symm

theorem gain_raise_diagonal (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C) (j : Fin n) (x : Fock n) :
    HasSum (fun k => ((k j:ℝ)+1)*f (up j k)/numberWeight k^6 *‖x k‖^2)
      (inner ℂ (gain j true x) (diagonal (fun k => f k/numberWeight k^4) C hC hf (gain j true x))).re := by
  have hz (k : NumberIndex n) (hk : k ∉ Set.range (up j)) :
      f k/numberWeight k^4 *‖gain j true x k‖^2=0 := by
    rcases index_cases j k with he | ⟨l,rfl⟩
    · simp [gain_raise_zero _ _ _ he]
    · exact (hk ⟨l,rfl⟩).elim
  have hh := (up_injective j).hasSum_iff hz |>.mpr
    (diagonal_quadratic (fun k => f k/numberWeight k^4) C hC hf (gain j true x))
  convert! hh using 1
  ext k
  simp only [Function.comp_def, gain_raise_sq]
  have hw : numberWeight (up j k) ≠ 0 := by linarith [numberWeight_one_le (up j k)]
  field_simp

theorem diagonal_selfAdjoint (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k| ≤ C) : IsSelfAdjoint (diagonal f C hC hf) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  apply HasSum.unique (lp.hasSum_inner (𝕜 := ℂ) (diagonal f C hC hf x) y)
  convert! lp.hasSum_inner (𝕜 := ℂ) x (diagonal f C hC hf y) using 1
  ext k
  simp only [diagonal_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem diagonal_mode_right (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C) (j : Fin n) (u : Bool) (x : Fock n) :
    HasSum (fun k => ((k j:ℝ)+(if u then 1 else 0))*f k/numberWeight k^6 *‖x k‖^2)
      (inner ℂ (modeBound j u x) (diagonal (fun k => f k/numberWeight k^4) C hC hf (inverseWeight 1 x))).re := by
  have he := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (diagonal_selfAdjoint _ C hC hf)
    (modeBound j u x) (inverseWeight 1 x)
  have ht := congrArg Complex.re he
  have hi : (inner ℂ (diagonal (fun k => f k/numberWeight k^4) C hC hf (modeBound j u x)) (inverseWeight 1 x)).re =
      (inner ℂ (inverseWeight 1 x) (diagonal (fun k => f k/numberWeight k^4) C hC hf (modeBound j u x))).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  exact (hi.symm.trans ht) ▸ diagonal_mode_left f C hC hf j u x
end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped BigOperators
variable {n : ℕ} {I : Type*}

theorem columnPairing_hasSum (r : ℝ) (x : I → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun i => columnPairing r (x i) Z) (pairing r x Z).re := by
  have ha (j : Fin n) (u : Bool) := CrossEnsemble.applied_summable hx (gain j u)
  have hb (j : Fin n) (u : Bool) := CrossEnsemble.applied_summable hx (modeBound j u)
  have hc := CrossEnsemble.applied_summable hx (inverseWeight 1)
  have h (j : Fin n) (u : Bool) :=
    ((CrossEnsemble.pairing_summable (ha j u) (ha j u) Z).hasSum.sub
      ((((CrossEnsemble.pairing_summable (hb j u) hc Z).hasSum).add
        ((CrossEnsemble.pairing_summable hc (hb j u) Z).hasSum)).mul_left (2:ℂ)⁻¹))
  have hh := (hasSum_sum fun j (_hj : j ∈ (Finset.univ : Finset (Fin n))) =>
    ((h j false).mul_left ((r+1:ℝ):ℂ)).add ((h j true).mul_left (r:ℂ))).mapL Complex.reCLM
  convert! hh using 1
  · ext i
    simp only [columnPairing, Complex.reCLM_apply, Complex.re_sum, Complex.add_re,
      Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    ext j
    norm_num
    ring

theorem mode_pairing_hasSum (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C) (x : Fock n) (j : Fin n) (u : Bool) :
    let Z := diagonal (fun k => f k/numberWeight k^4) C hC hf
    HasSum (fun k => ((k j:ℝ)+(if u then 1 else 0))*f k/numberWeight k^6*‖x k‖^2)
      (((inner ℂ (inverseWeight 1 x) (Z (modeBound j u x))).re+
        (inner ℂ (modeBound j u x) (Z (inverseWeight 1 x))).re)/2) := by
  have h₁ := diagonal_mode_left f C hC hf j u x
  have h₂ := diagonal_mode_right f C hC hf j u x
  have hh := (h₁.add h₂).div_const 2
  convert! hh using 1
  ext k
  ring

theorem component_pairing_hasSum (r : ℝ) (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C) (x : Fock n) (j : Fin n) :
    HasSum
      (fun k => ((r+1)*(k j:ℝ)*(f (down j k)-f k)+r*((k j:ℝ)+1)*(f (up j k)-f k))/numberWeight k^6*‖x k‖^2)
      (componentPairing r x (diagonal (fun k => f k/numberWeight k^4) C hC hf) j) := by
  have h₁ := (gain_lower_diagonal f C hC hf j x).sub (mode_pairing_hasSum f C hC hf x j false)
  have h₂ := (gain_raise_diagonal f C hC hf j x).sub (mode_pairing_hasSum f C hC hf x j true)
  have hh := (h₁.mul_left (r+1)).add (h₂.mul_left r)
  convert! hh using 1
  ext k
  simp only [Bool.false_eq_true, ↓reduceIte]
  ring

theorem drift_column (r : ℝ) (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C) (x : Fock n) :
    HasSum (fun k => drift r f k/numberWeight k^6*‖x k‖^2)
      (columnPairing r x (diagonal (fun k => f k/numberWeight k^4) C hC hf)) := by
  have hh := hasSum_sum fun j (_hj : j ∈ (Finset.univ : Finset (Fin n))) =>
    component_pairing_hasSum r f C hC hf x j
  convert! hh using 1
  · ext k
    simp only [drift, Finset.sum_div, Finset.sum_mul]
end WeightedGenerator

namespace WeightedShift
variable {I K : Type*}
theorem family_coordinates_summable (x : I → H K) (hx : Summable (fun i => ‖x i‖^2)) :
    Summable (fun ik : I × K => ‖x ik.1 ik.2‖^2) := by
  exact (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    ⟨fun i => (hasSum_square (x i)).summable,
      by simpa only [(hasSum_square _).tsum_eq] using hx⟩
end WeightedShift

namespace EntropyPhotonNumber
open QuantumTrace WeightedShift Annihilation
variable {n : ℕ}

theorem weightedRoot_row (m : ℕ) (ρ : State n) (hm : FiniteMoment (2*m) ρ)
    (k : NumberIndex n) :
    HasSum (fun i => ‖weightedRoot m ρ hm i k‖^2)
      (numberWeight k^(2*m)*(entry ρ.op k k).re) := by
  have hh := (TraceEnsemble.hasSum_quadratic (rootColumn_norm ρ).summable (numberKet k)).mul_left (numberWeight k^(2*m))
  rw [rootColumn_operator] at hh
  convert! hh using 1
  ext i
  simp only [weightedRoot_apply, numberKet, lp.inner_single_left, RCLike.inner_apply,
    map_one, mul_one, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    ← pow_mul, mul_comm m 2]

theorem thermalGenerator_drift (r : ℝ) (ρ : State n) (hm : FiniteMoment 6 ρ)
    (f : NumberIndex n → ℝ) (C D : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C)
    (hd : ∀ k, |WeightedGenerator.drift r f k/numberWeight k^6| ≤ D) :
    HasSum (fun k => WeightedGenerator.drift r f k*(entry ρ.op k k).re)
      (WeightedGenerator.pairing r (weightedRoot 3 ρ hm)
        (diagonal (fun k => f k/numberWeight k^4) C hC hf)).re := by
  let x := weightedRoot 3 ρ hm
  let a := fun (i k : NumberIndex n) => WeightedGenerator.drift r f k/numberWeight k^6*‖x i k‖^2
  have hx := weightedRoot_summable 3 ρ hm
  have hp : Summable (Function.uncurry a) := by
    apply ((family_coordinates_summable x hx).mul_left D).of_norm_bounded
    intro ik
    change ‖WeightedGenerator.drift r f ik.2/numberWeight ik.2^6*‖x ik.1 ik.2‖^2‖ ≤ D*‖x ik.1 ik.2‖^2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖x ik.1 ik.2‖)]
    exact mul_le_mul_of_nonneg_right (hd _) (sq_nonneg _)
  have hc (i : NumberIndex n) := WeightedGenerator.drift_column r f C hC hf (x i)
  have hr (k : NumberIndex n) : HasSum (fun i => a i k)
      (WeightedGenerator.drift r f k*(entry ρ.op k k).re) := by
    have he := (weightedRoot_row 3 ρ hm k).mul_left (WeightedGenerator.drift r f k/numberWeight k^6)
    convert! he using 1
    have hne : numberWeight k ≠ 0 := by linarith [numberWeight_one_le k]
    field_simp
  have he : (∑' k, ∑' i, a i k)=(WeightedGenerator.pairing r x
      (diagonal (fun k => f k/numberWeight k^4) C hC hf)).re := by
    rw [hp.tsum_comm]
    simp only [a, (hc _).tsum_eq]
    exact (WeightedGenerator.columnPairing_hasSum r x hx _).tsum_eq
  have hs := hp.prod_symm.prod.hasSum
  change HasSum (fun k => ∑' i, a i k) (∑' k, ∑' i, a i k) at hs
  rw [he] at hs
  simpa only [(hr _).tsum_eq] using hs
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
open OAI OAI.EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open QuantumTrace WeightedShift Annihilation


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.thermalGenerator_drift := @_root_.OAI.EntropyPhotonNumber.thermalGenerator_drift
