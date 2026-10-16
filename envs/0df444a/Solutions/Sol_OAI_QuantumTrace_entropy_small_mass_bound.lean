-- Prove2me | solution 1 for OAI.QuantumTrace.entropy_small_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:18:44.624702+00:00
-- url     : https://prove2.me/submissions/db1761f7-9899-407e-af3e-af526c317583

-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean:L704-L760
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.entropy_small_mass_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Theorems.Thm_OAI_QuantumTrace_negMulLog_le_crossEntropy

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

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section

theorem entropy_summable_le_reference {ι : Type*} (p a : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpu : ∀ i, p i ≤ 1) (ha : ∀ i, 0 < a i)
    {m : ℝ} (hpm : HasSum p m) (ham : HasSum a m)
    (hc : Summable (fun i => p i * (-Real.log (a i)))) :
    Summable (fun i => Real.negMulLog (p i)) ∧
    (∑' i, Real.negMulLog (p i)) ≤ ∑' i, p i * (-Real.log (a i)) := by
  have he0 (i : ι) : 0 ≤ Real.negMulLog (p i) := Real.negMulLog_nonneg (hp i) (hpu i)
  have hle (i : ι) := negMulLog_le_crossEntropy (hp i) (ha i)
  have hsum := (ham.summable.sub hpm.summable).add hc
  have he : Summable (fun i => Real.negMulLog (p i)) :=
    Summable.of_nonneg_of_le he0 hle hsum
  refine ⟨he, ?_⟩
  have hh := he.tsum_le_tsum hle hsum
  rw [(ham.summable.sub hpm.summable).tsum_add hc,
    ham.summable.tsum_sub hpm.summable, hpm.tsum_eq, ham.tsum_eq] at hh
  simpa only [sub_self, zero_add] using hh

theorem entropy_small_mass_bound {n : ℕ} (p : (Fin n → ℕ) → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hpu : ∀ k, p k ≤ 1) {q : ℝ} (hq : HasSum p q)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * p k)) :
    Summable (fun k => Real.negMulLog (p k)) ∧
    (∑' k, Real.negMulLog (p k)) ≤
      (n + 1 : ℝ) * Real.negMulLog q + n * q ^ 2 +
        (∑' k, (∑ j, (k j : ℝ)) * p k) * q := by
  have hq0 : 0 ≤ q := hq.nonneg hp
  by_cases hz : q = 0
  · have hpz : ∀ k, p k = 0 := by
      intro k
      apply le_antisymm _ (hp k)
      simpa only [hq.tsum_eq, hz] using hq.summable.le_tsum k (fun j _ => hp j)
    simp only [hpz, Real.negMulLog_zero, tsum_zero, hz, zero_pow (by omega : 2 ≠ 0),
      mul_zero, zero_add, le_refl, and_true]
    exact summable_zero
  have hqp : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hz)
  have hr : 0 < q⁻¹ := inv_pos.mpr hqp
  let a : (Fin n → ℕ) → ℝ := fun k => q * thermalWeight n q⁻¹ k
  have ha : ∀ k, 0 < a k := fun k => mul_pos hqp (thermalWeight_pos n hr k)
  have haq : HasSum a q := by
    simpa only [mul_one] using (hasSum_thermalWeight n hr).mul_left q
  have hlog (k : Fin n → ℕ) : -Real.log (a k) =
      -Real.log q + (-Real.log (thermalWeight n q⁻¹ k)) := by
    change -Real.log (q * thermalWeight n q⁻¹ k) = _
    rw [Real.log_mul hz (thermalWeight_pos n hr k).ne']
    ring
  have hcross : Summable (fun k => p k * (-Real.log (a k))) := by
    simp only [hlog, mul_add]
    exact (hq.summable.mul_right _).add (summable_thermal_crossEntropy hq.summable hE hr)
  obtain ⟨he, hbound⟩ := entropy_summable_le_reference p a hp hpu ha hq haq hcross
  refine ⟨he, hbound.trans ?_⟩
  have hlog1 : Real.log (q⁻¹ + 1) = Real.log (q + 1) - Real.log q := by
    rw [← Real.log_div (by positivity : q + 1 ≠ 0) hz]
    congr 1
    field_simp
    ring
  have hlog2 : Real.log ((q⁻¹ + 1) / q⁻¹) = Real.log (q + 1) := by
    congr 1
    field_simp
    ring
  have hex (k : Fin n → ℕ) : p k * (-Real.log (a k)) =
      p k * (-(n + 1) * Real.log q) +
      (((n : ℝ) * p k) + (∑ j, (k j : ℝ)) * p k) * Real.log (q + 1) := by
    rw [hlog, log_thermalWeight n hr k, hlog1, hlog2]
    ring
  simp only [hex]
  rw [(hq.summable.mul_right _).tsum_add (((hq.summable.mul_left _).add hE).mul_right _),
    tsum_mul_right, tsum_mul_right, (hq.summable.mul_left _).tsum_add hE,
    tsum_mul_left, hq.tsum_eq]
  have hepos : 0 ≤ ∑' k, (∑ j, (k j : ℝ)) * p k :=
    tsum_nonneg (fun k => mul_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (hp k))
  have hl : Real.log (q + 1) ≤ q := by
    simpa only [add_sub_cancel_right] using Real.log_le_sub_one_of_pos (by linarith : 0 < q + 1)
  have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (n : ℝ) * q + ∑' k, (∑ j, (k j : ℝ)) * p k)
  dsimp [Real.negMulLog]
  nlinarith

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


theorem solution : type_of% @_root_.OAI.QuantumTrace.entropy_small_mass_bound := @_root_.OAI.QuantumTrace.entropy_small_mass_bound
