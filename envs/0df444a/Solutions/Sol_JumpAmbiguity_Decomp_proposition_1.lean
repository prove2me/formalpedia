-- Prove2me | solution 1 for JumpAmbiguity.Decomp.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:36:08.261326+00:00
-- url     : https://prove2.me/submissions/1e20fbdb-b6d4-4a5e-888f-4632cdc1c443

import Mathlib
import Definitions.Def_JumpAmbiguity_Decomp_Model

namespace JumpAmbiguity.Decomp
open MeasureTheory

lemma pw_bound (c phi f : ℝ) (hphi : 0 < phi) (hf : 0 < f) :
    (1 - Real.exp (-phi * c)) / phi ≤ c * f + (f * Real.log f + 1 - f) / phi ∧
    ((1 - Real.exp (-phi * c)) / phi = c * f + (f * Real.log f + 1 - f) / phi →
      f = Real.exp (-phi * c)) := by
  set p := Real.exp (-phi * c) with hp
  have hp0 : 0 < p := Real.exp_pos _
  have hlogp : Real.log p = -phi * c := Real.log_exp _
  have key : (c * f + (f * Real.log f + 1 - f) / phi) - (1 - p) / phi =
      (f * (Real.log f - Real.log p) - f + p) / phi := by
    rw [hlogp]; field_simp; ring
  have hdiv : Real.log (p / f) = Real.log p - Real.log f :=
    Real.log_div hp0.ne' hf.ne'
  constructor
  · have h1 := Real.log_le_sub_one_of_pos (div_pos hp0 hf)
    rw [hdiv] at h1
    have h2 : 0 ≤ f * (Real.log f - Real.log p) - f + p := by
      have := mul_le_mul_of_nonneg_left h1 hf.le
      have e : f * (p / f - 1) = p - f := by field_simp
      rw [e] at this
      linarith
    have : 0 ≤ (f * (Real.log f - Real.log p) - f + p) / phi := div_nonneg h2 hphi.le
    linarith
  · intro heq
    by_contra hne
    have hne' : p / f ≠ 1 := by
      intro h; apply hne; field_simp at h; linarith
    have h1 := Real.log_lt_sub_one_of_pos (div_pos hp0 hf) hne'
    rw [hdiv] at h1
    have h2 : 0 < f * (Real.log f - Real.log p) - f + p := by
      have := mul_lt_mul_of_pos_left h1 hf
      have e : f * (p / f - 1) = p - f := by field_simp
      rw [e] at this
      linarith
    have : 0 < (f * (Real.log f - Real.log p) - f + p) / phi := div_pos h2 hphi
    linarith

lemma psiStar_eq {m n : ℕ} (M : Market m n) (hγ : M.γ ≠ 1) (a y : ℝ) :
    M.psiStar a y = Real.exp (-M.phi * M.cost a y) := by
  unfold Market.psiStar Market.cost
  congr 1
  have : (1 - M.γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have : (M.γ - 1) ≠ 0 := sub_ne_zero.mpr hγ
  field_simp
  ring

lemma psiStar_pos {m n : ℕ} (M : Market m n) (a y : ℝ) : 0 < M.psiStar a y :=
  Real.exp_pos _

lemma psiStar_meas {m n : ℕ} (M : Market m n) (a : ℝ) : Measurable (M.psiStar a) := by
  unfold Market.psiStar
  fun_prop

lemma thetaStar_pos {m n : ℕ} (M : Market m n) (k : Fin n) (a : ℝ)
    [IsProbabilityMeasure (M.Phi k)] (h : Integrable (M.psiStar a) (M.Phi k)) :
    0 < M.thetaStar k a :=
  integral_exp_pos h

lemma star_integrand {m n : ℕ} (M : Market m n) (hγ : M.γ ≠ 1) (hphi : 0 < M.phi)
    (k : Fin n) (a : ℝ) (hθ : 0 < M.thetaStar k a) (y : ℝ) :
    M.integrand a (M.thetaStar k a) (M.varphiStar k a) y = (1 - M.psiStar a y) / M.phi := by
  have h1 : M.thetaStar k a * M.varphiStar k a y = M.psiStar a y := by
    unfold Market.varphiStar; field_simp
  unfold Market.integrand
  rw [h1]
  have hl : Real.log (M.psiStar a y) = -M.phi * M.cost a y := by
    rw [psiStar_eq M hγ, Real.log_exp]
  rw [hl]
  field_simp
  ring

lemma integrand_bound {m n : ℕ} (M : Market m n) (hγ : M.γ ≠ 1) (hphi : 0 < M.phi)
    (a θ : ℝ) (varphi : ℝ → ℝ) (y : ℝ) (hf : 0 < θ * varphi y) :
    (1 - M.psiStar a y) / M.phi ≤ M.integrand a θ varphi y ∧
    ((1 - M.psiStar a y) / M.phi = M.integrand a θ varphi y →
      θ * varphi y = M.psiStar a y) := by
  have := pw_bound (M.cost a y) M.phi (θ * varphi y) hphi hf
  rw [psiStar_eq M hγ]
  exact this

theorem proposition_1_aux {m n : ℕ} (M : Market m n) (hS : M.Standing)
    (hI : M.JumpIntegrable) (k : Fin n) (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    M.AdmissiblePair k a (M.thetaStar k a) (M.varphiStar k a) ∧
      IsLeast {v : ℝ | ∃ θ varphi, M.AdmissiblePair k a θ varphi ∧
        v = M.innerObj k a θ varphi}
        (M.innerObj k a (M.thetaStar k a) (M.varphiStar k a)) ∧
      ∀ θ (varphi : ℝ → ℝ), M.AdmissiblePair k a θ varphi →
        M.innerObj k a θ varphi = M.innerObj k a (M.thetaStar k a) (M.varphiStar k a) →
          θ = M.thetaStar k a ∧ varphi =ᵐ[M.Phi k] M.varphiStar k a := by
  obtain ⟨-, -, -, -, hprob, hnull, hlam, -, hγ, hphi⟩ := hS
  have := hprob k
  have hpsi : Integrable (M.psiStar a) (M.Phi k) := (hI k a ha).1
  have hθ := thetaStar_pos M k a hpsi
  have hstarInt : Integrable (M.integrand a (M.thetaStar k a) (M.varphiStar k a)) (M.Phi k) := by
    have : M.integrand a (M.thetaStar k a) (M.varphiStar k a) =
        fun y => (1 - M.psiStar a y) / M.phi := funext (star_integrand M hγ hphi k a hθ)
    rw [this]
    exact ((integrable_const 1).sub hpsi).div_const _
  have hae : ∀ᵐ y ∂(M.Phi k), y ∈ Set.Ioi (-1 : ℝ) := mem_ae_iff.mpr (hnull k)
  have hadm : M.AdmissiblePair k a (M.thetaStar k a) (M.varphiStar k a) := by
    refine ⟨hθ, ?_, ?_, ?_, ?_, hstarInt⟩
    · exact (psiStar_meas M a).div_const _
    · intro y _; exact div_pos (psiStar_pos M a y) hθ
    · exact hpsi.div_const _
    · unfold Market.varphiStar
      rw [integral_div]
      exact div_self hθ.ne'
  -- the integrand of any admissible pair dominates the star integrand a.e.
  have hdom : ∀ θ (varphi : ℝ → ℝ), M.AdmissiblePair k a θ varphi →
      ∀ᵐ y ∂(M.Phi k), (1 - M.psiStar a y) / M.phi ≤ M.integrand a θ varphi y ∧
        ((1 - M.psiStar a y) / M.phi = M.integrand a θ varphi y →
          θ * varphi y = M.psiStar a y) := by
    intro θ varphi hp
    filter_upwards [hae] with y hy
    exact integrand_bound M hγ hphi a θ varphi y (mul_pos hp.1 (hp.2.2.1 y hy))
  have hstar_eq : ∀ y, M.integrand a (M.thetaStar k a) (M.varphiStar k a) y =
      (1 - M.psiStar a y) / M.phi := star_integrand M hγ hphi k a hθ
  have hle : ∀ θ (varphi : ℝ → ℝ), M.AdmissiblePair k a θ varphi →
      M.innerObj k a (M.thetaStar k a) (M.varphiStar k a) ≤ M.innerObj k a θ varphi := by
    intro θ varphi hp
    unfold Market.innerObj
    apply mul_le_mul_of_nonneg_left _ (hlam k).le
    apply integral_mono_ae hstarInt hp.2.2.2.2.2
    filter_upwards [hdom θ varphi hp] with y hy
    rw [hstar_eq]; exact hy.1
  refine ⟨hadm, ⟨⟨_, _, hadm, rfl⟩, ?_⟩, ?_⟩
  · rintro v ⟨θ, varphi, hp, rfl⟩
    exact hle θ varphi hp
  · intro θ varphi hp heq
    unfold Market.innerObj at heq
    have heq' := mul_left_cancel₀ (hlam k).ne' heq
    have hnn : 0 ≤ᵐ[M.Phi k] (M.integrand a θ varphi -
        M.integrand a (M.thetaStar k a) (M.varphiStar k a)) := by
      filter_upwards [hdom θ varphi hp] with y hy
      simp only [Pi.zero_apply, Pi.sub_apply]
      rw [hstar_eq]; linarith [hy.1]
    have hint0 : ∫ y, (M.integrand a θ varphi -
        M.integrand a (M.thetaStar k a) (M.varphiStar k a)) y ∂(M.Phi k) = 0 := by
      simp only [Pi.sub_apply]
      rw [integral_sub hp.2.2.2.2.2 hstarInt, heq', sub_self]
    have hz := (integral_eq_zero_iff_of_nonneg_ae hnn (hp.2.2.2.2.2.sub hstarInt)).mp hint0
    have hprod : ∀ᵐ y ∂(M.Phi k), θ * varphi y = M.psiStar a y := by
      filter_upwards [hdom θ varphi hp, hz] with y hy hzy
      apply hy.2
      simp only [Pi.zero_apply, Pi.sub_apply] at hzy
      rw [← hstar_eq]; linarith
    have hθeq : θ = M.thetaStar k a := by
      have h1 : ∫ y, θ * varphi y ∂(M.Phi k) = θ := by
        rw [integral_const_mul, hp.2.2.2.2.1, mul_one]
      rw [← h1, integral_congr_ae hprod]
      rfl
    refine ⟨hθeq, ?_⟩
    filter_upwards [hprod] with y hy
    unfold Market.varphiStar
    rw [← hy, ← hθeq]
    field_simp [hp.1.ne']

end JumpAmbiguity.Decomp

open JumpAmbiguity.Decomp

theorem solution {m n : ℕ} (M : Market m n) (hS : M.Standing)
    (hI : M.JumpIntegrable) (k : Fin n) (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    M.AdmissiblePair k a (M.thetaStar k a) (M.varphiStar k a) ∧
      IsLeast {v : ℝ | ∃ θ varphi, M.AdmissiblePair k a θ varphi ∧
        v = M.innerObj k a θ varphi}
        (M.innerObj k a (M.thetaStar k a) (M.varphiStar k a)) ∧
      ∀ θ (varphi : ℝ → ℝ), M.AdmissiblePair k a θ varphi →
        M.innerObj k a θ varphi = M.innerObj k a (M.thetaStar k a) (M.varphiStar k a) →
          θ = M.thetaStar k a ∧ varphi =ᵐ[M.Phi k] M.varphiStar k a :=
  JumpAmbiguity.Decomp.proposition_1_aux M hS hI k a ha
