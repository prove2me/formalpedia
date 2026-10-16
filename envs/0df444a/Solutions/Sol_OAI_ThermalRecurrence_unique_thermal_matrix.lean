-- Prove2me | solution 1 for OAI.ThermalRecurrence.unique_thermal_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:57:14.856435+00:00
-- url     : https://prove2.me/submissions/c18741a5-ba3e-4b25-8e0e-81f1c45490f5

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/ThermalLimit.lean:L243-L282
-- (upload_full_project.md Phase 4): solution for node OAI.ThermalRecurrence.unique_thermal_matrix. The node keeps its source
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

-- ---- from OAI.InformationTheory.PhotonNumber.ThermalLimit ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

end ThermalMetric

namespace EntropyPhotonNumber.GibbsData
open WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

namespace ThermalRecurrence

section
variable {J : Type*} [Fintype J] [DecidableEq J]

theorem lower_sum {p : J → ℕ} {j : J} (hp : 0 < p j) :
    (∑ k, lower p j k) + 1 = ∑ k, p k := by
  rw [show (∑ k, lower p j k) = (p j-1) + ∑ k ∈ Finset.univ.erase j, p k by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [lower_same]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    exact Function.update_of_ne (Finset.ne_of_mem_erase hk) _ _]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  omega

omit [Fintype J] in

theorem entry_zero_of_lt {r : ℝ} (hr : 0 < r)
    {M : (J → ℕ) → (J → ℕ) → ℂ} (hM : Balance r M)
    (j : J) {p b : J → ℕ} (hp : b j < p j) : M p b = 0 := by
  have hall (m : ℕ) : ∀ (p b : J → ℕ), b j = m → b j < p j → M p b = 0 := by
    induction m with
    | zero =>
      intro p b hb hpb
      have hpj : 0 < (p j : ℝ) := Nat.cast_pos.mpr (by omega)
      have hz := hM j p b (by omega)
      have hne : (r+1)*Real.sqrt (p j : ℝ) ≠ 0 := by positivity
      simp only [hb, Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_smul] at hz
      exact (smul_eq_zero.mp hz).resolve_left hne
    | succ m ih =>
      intro p b hb hpb
      have hprev := ih (lower p j) (lower b j) (by simp [hb]) (by simp; omega)
      have hpj : 0 < (p j : ℝ) := Nat.cast_pos.mpr (by omega)
      have hz := hM j p b (by omega)
      rw [hprev, smul_zero] at hz
      exact (smul_eq_zero.mp hz).resolve_left (by positivity)
  exact hall (b j) p b rfl hp

omit [Fintype J] in

theorem off_diagonal_zero {r : ℝ} (hr : 0 < r)
    {M : (J → ℕ) → (J → ℕ) → ℂ} (hM : Balance r M)
    (hstar : ∀ p b, M b p = conj (M p b)) {p b : J → ℕ} (hne : p ≠ b) : M p b = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  rcases lt_or_gt_of_ne hj with h | h
  · have hb := entry_zero_of_lt hr hM j h
    rw [hstar] at hb
    simpa using congrArg conj hb
  · exact entry_zero_of_lt hr hM j h

omit [Fintype J] in

theorem diagonal_step {r : ℝ} (hr : 0 < r)
    {M : (J → ℕ) → (J → ℕ) → ℂ} (hM : Balance r M)
    {p : J → ℕ} {j : J} (hp : 0 < p j) :
    M p p = (r/(r+1)) • M (lower p j) (lower p j) := by
  have hh := hM j p p hp
  have ha : (r+1)*Real.sqrt (p j:ℝ) ≠ 0 := by positivity
  have he : ((r+1)*Real.sqrt (p j:ℝ)) •
      ((r/(r+1)) • M (lower p j) (lower p j)) =
        (r*Real.sqrt (p j:ℝ)) • M (lower p j) (lower p j) := by
    rw [smul_smul]
    congr 1
    field_simp
  apply (smul_right_injective _ ha)
  exact hh.trans he.symm

theorem diagonal_formula {r : ℝ} (hr : 0 < r)
    {M : (J → ℕ) → (J → ℕ) → ℂ} (hM : Balance r M) (p : J → ℕ) :
    M p p = (r/(r+1))^(∑ j, p j) • M 0 0 := by
  have hall (m : ℕ) : ∀ p : J → ℕ, (∑ j, p j) = m →
      M p p = (r/(r+1))^m • M 0 0 := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro p hp
      by_cases hzero : p = 0
      · subst p
        simp at hp
        subst m
        simp
      · obtain ⟨j, hj⟩ := Function.ne_iff.mp hzero
        change p j ≠ 0 at hj
        have hj0 : 0 < p j := Nat.pos_of_ne_zero hj
        have hsum := lower_sum hj0
        rw [hp] at hsum
        rw [diagonal_step hr hM hj0, ih (∑ k, lower p j k) (by omega) (lower p j) rfl,
          smul_smul, ← pow_succ']
        rw [hsum]
  exact hall _ p rfl

end

theorem thermalWeight_eq (n : ℕ) (r : ℝ) (p : Fin n → ℕ) :
    QuantumTrace.thermalWeight n r p = (r+1)⁻¹^n * (r/(r+1))^(∑ j, p j) := by
  simp [QuantumTrace.thermalWeight, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem unique_thermal_matrix (n : ℕ) {r : ℝ} (hr : 0 < r)
    {M : (Fin n → ℕ) → (Fin n → ℕ) → ℂ} (hM : Balance r M)
    (hstar : ∀ p b, M b p = conj (M p b))
    (htrace : HasSum (fun p => (M p p).re) 1) (p b : Fin n → ℕ) :
    M p b = if p = b then (QuantumTrace.thermalWeight n r p : ℂ) else 0 := by
  let c : ℂ := (r+1)^n • M 0 0
  have hr1 : r+1 ≠ 0 := by positivity
  have hc0 : c.im = 0 := by
    have he := congrArg Complex.im (hstar 0 0)
    dsimp [c]
    simp only [Complex.conj_im] at he
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    have hz : (M 0 0).im = 0 := by linarith
    rw [hz, mul_zero]
  have hf (a : Fin n → ℕ) : M a a = QuantumTrace.thermalWeight n r a • c := by
    have hw : QuantumTrace.thermalWeight n r a * (r+1)^n =
        (r/(r+1))^(∑ j, a j) := by
      rw [thermalWeight_eq n r a, inv_pow]
      field_simp
    calc
      M a a = (r/(r+1))^(∑ j, a j) • M 0 0 := diagonal_formula hr hM a
      _ = (QuantumTrace.thermalWeight n r a * (r+1)^n) • M 0 0 := by rw [hw]
      _ = QuantumTrace.thermalWeight n r a • c := (smul_smul _ _ _).symm
  have hs := ((QuantumTrace.hasSum_thermalWeight n hr).mul_right c.re)
  have hc1 : c.re = 1 := by
    have hefun : (fun a : Fin n → ℕ => (M a a).re) =
        (fun a => QuantumTrace.thermalWeight n r a * c.re) := by
      funext a
      rw [hf]
      simp
    rw [hefun] at htrace
    simpa only [one_mul] using hs.unique htrace
  have hc : c = 1 := Complex.ext hc1 hc0
  by_cases he : p = b
  · subst b
    rw [ite_eq_left rfl, hf, hc]
    simp
  · rw [ite_eq_right he]
    exact off_diagonal_zero hr hM hstar he

end ThermalRecurrence

namespace EntropyPhotonNumber
open Filter Topology Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ}

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate Topology

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder

namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)
end ThermalSetup
end

section
open QuantumTrace Annihilation Filter ThermalMetric

namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)
end ThermalSetup
end

open QuantumTrace ThermalMetric Filter

namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)
end ThermalSetup
end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.ThermalRecurrence
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate


theorem solution : type_of% @_root_.OAI.ThermalRecurrence.unique_thermal_matrix := @_root_.OAI.ThermalRecurrence.unique_thermal_matrix
