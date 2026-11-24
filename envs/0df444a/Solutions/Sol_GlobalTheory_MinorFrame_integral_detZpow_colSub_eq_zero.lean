-- Prove2me | solution 1 for GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:55.15929+00:00
-- url     : https://prove2.me/submissions/119f2150-c8fa-4cfe-8dd4-5a8edd77cba1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralDetCharacterFockColumnSubstitutionEqZero
import Theorems.Thm_GlobalTheory_MinorFrame_colSub_mul
import Theorems.Thm_GlobalTheory_MinorFrame_sum_scalAt_eq_zero
import Theorems.Thm_GlobalTheory_MinorFrame_prod_det_scalAt_zpow
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Classical MeasureTheory
noncomputable section
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open MvPolynomial
namespace GlobalTheory.MinorFrame
theorem _root_.solution :
    ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ) (τ₀ : ι), 0 < a → 0 < m τ₀ → ∀ {K : Type} [Group K]
      [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
    ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)),
      (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) →
      Function.Surjective ρ →
    ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
        Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) ∂ν = 0 := by
  intro ι _ a d m τ₀ ha hm K _ _ ν hν hinv ρ _ hρ Λ P
  set B : K → ι → Matrix (Fin a) (Fin a) ℂ := fun g τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) with hB_def
  set c : K → ℂ := fun g => ∏ τ, (B g τ).det ^ (m τ) with hc_def
  set f : K → ℂ := fun g => c g * Λ (colSub (B g) P) with hf_def
  show ∫ g, f g ∂ν = 0
  by_cases hint : Integrable f ν
  swap
  · exact integral_undef hint

  have hinvar : ∀ u : K, Integrable (fun x => f (u * x)) ν ∧ ∫ x, f (u * x) ∂ν = ∫ x, f x ∂ν := by
    intro u
    have hmap : Measure.map (fun x => u * x) ν = ν := map_mul_left_eq_self ν u
    have hae : AEMeasurable (fun x => u * x) ν := by
      by_contra h
      rw [Measure.map_of_not_aemeasurable h] at hmap
      exact (IsProbabilityMeasure.ne_zero ν) hmap.symm
    refine ⟨?_, ?_⟩
    · have : Integrable f (Measure.map (fun x => u * x) ν) := by rw [hmap]; exact hint
      exact this.comp_aemeasurable hae
    · have h := integral_map hae (f := f) (by rw [hmap]; exact hint.aestronglyMeasurable)
      rw [hmap] at h
      exact h.symm

  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m τ₀ := ⟨(m τ₀).toNat, Int.toNat_of_nonneg hm.le⟩
  have hnpos : 0 < n := by omega
  set N := a * n with hN_def
  have hN : 0 < N := Nat.mul_pos ha hnpos
  set M := N + P.totalDegree + 1 with hM_def
  have hM0 : M ≠ 0 := by omega
  set ω := Complex.exp (2 * Real.pi * Complex.I / M) with hω_def
  have hω : IsPrimitiveRoot ω M := Complex.isPrimitiveRoot_exp M hM0
  have hmemU : ∀ k : ℕ, ((ω ^ k) • (1 : Matrix (Fin a) (Fin a) ℂ)) ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    intro k
    have hnorm : ‖ω ^ k‖ = 1 := by rw [norm_pow, hω.norm'_eq_one hM0, one_pow]
    have hc : ω ^ k * star (ω ^ k) = 1 := by
      rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      hc, one_smul]
  let U : ℕ → ι → Matrix.unitaryGroup (Fin a) ℂ := fun k τ => if τ = τ₀ then ⟨(ω ^ k) • 1, hmemU k⟩ else 1
  have hU : ∀ k τ, (U k τ : Matrix (Fin a) (Fin a) ℂ) = scalAt τ₀ (ω ^ k) τ := by
    intro k τ
    simp only [U, scalAt]
    split_ifs <;> rfl
  choose u hu using fun k => hρ (U k)

  have hpt : ∀ k g, f (u k * g) = c g * Λ ((ω ^ k) ^ N • colSub (B g) (colSub (scalAt τ₀ (ω ^ k)) P)) := by
    intro k g
    have hBu : B (u k * g) = fun τ => B g τ * scalAt τ₀ (ω ^ k) τ := by
      funext τ
      simp only [hB_def, map_mul, Pi.mul_apply, hu k]
      rw [Submonoid.coe_mul, hU k τ]
      simp only [scalAt]
      split_ifs <;> simp [Matrix.smul_mul, Matrix.mul_smul]
    simp only [hf_def, hc_def]
    rw [hBu, colSub_mul, map_smul, smul_eq_mul]
    simp only [Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
    rw [prod_det_scalAt_zpow τ₀ (ω ^ k) m n hn]
    ring
  have hsum0 : ∀ g, ∑ k ∈ Finset.range M, f (u k * g) = 0 := by
    intro g
    simp only [hpt, ← Finset.mul_sum, ← map_sum]
    have : ∑ k ∈ Finset.range M, (ω ^ k) ^ N • colSub (B g) (colSub (scalAt τ₀ (ω ^ k)) P) =
        colSub (B g) (∑ k ∈ Finset.range M, (ω ^ k) ^ N • colSub (scalAt τ₀ (ω ^ k)) P) := by
      rw [map_sum]; simp only [map_smul]
    rw [this, sum_scalAt_eq_zero τ₀ N hN P hω, map_zero, map_zero, mul_zero]
  have hkey : (M : ℂ) * ∫ x, f x ∂ν = 0 := by
    calc (M : ℂ) * ∫ x, f x ∂ν = ∑ k ∈ Finset.range M, ∫ x, f (u k * x) ∂ν := by
          rw [Finset.sum_congr rfl fun k _ => (hinvar (u k)).2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ∫ x, ∑ k ∈ Finset.range M, f (u k * x) ∂ν :=
          (integral_finset_sum _ fun k _ => (hinvar (u k)).1).symm
      _ = 0 := by simp [hsum0]
  exact (mul_eq_zero.1 hkey).resolve_left (by exact_mod_cast hM0)
end GlobalTheory.MinorFrame
