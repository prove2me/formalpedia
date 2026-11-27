-- Prove2me | solution 1 for JointMixND.QuadOT.Supplement.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:50.836813+00:00
-- url     : https://prove2.me/submissions/328c0db4-d3b7-4bf9-ab86-cb48233c865c

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Basic
import Definitions.Def_JointMixND_QuadOT_Supplement_Elliptical

open MeasureTheory ProbabilityTheory Matrix

open JointMixND
open JointMixND.QuadOT
open JointMixND.QuadOT.Supplement

theorem solution {n : ℕ} (ψ : ℝ → ℝ) (μ : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (P : Measure (Fin n → ℝ)) (hP : IsElliptical ψ μ S P) :
    IsJointMix P ↔
      ((1 : Fin n → ℝ) ⬝ᵥ (S *ᵥ (1 : Fin n → ℝ)) = 0 ∨ ∀ s : ℝ, 0 ≤ s → ψ s = 1) := by
        obtain ⟨hprob, hS, hchar⟩ := hP
        set v : ℝ := (1 : Fin n → ℝ) ⬝ᵥ (S *ᵥ (1 : Fin n → ℝ)) with hv
        set m : ℝ := ∑ j, μ j with hm
        have hv0 : 0 ≤ v := by
          have h := hS.dotProduct_mulVec_nonneg (1 : Fin n → ℝ)
          simpa [hv] using h
        have hquad : ∀ u : ℝ, (fun _ : Fin n => u) ⬝ᵥ (S *ᵥ (fun _ : Fin n => u)) = u ^ 2 * v := by
          intro u
          have hu : (fun _ : Fin n => u) = u • (1 : Fin n → ℝ) := by
            ext i; simp
          rw [hu, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, ← hv]
          simp only [smul_eq_mul]
          ring
        have hline : ∀ u : ℝ, ∫ x, Complex.exp (((u * ∑ j, x j : ℝ) : ℂ) * Complex.I) ∂P =
            Complex.exp (((u * m : ℝ) : ℂ) * Complex.I) * ((ψ (u ^ 2 * v) : ℝ) : ℂ) := by
          intro u
          have h := hchar (fun _ => u)
          rw [hquad u] at h
          simpa only [← Finset.mul_sum] using h
        have hψ0 : ψ 0 = 1 := by
          have h := hline 0
          have h2 : (1 : ℂ) = ((ψ 0 : ℝ) : ℂ) := by simpa using h
          exact_mod_cast h2.symm
        have hmeas : Measurable (fun x : Fin n → ℝ => ∑ i, x i) := by fun_prop
        constructor
        · rintro ⟨c, hc⟩
          have hexp : ∀ u : ℝ, Complex.exp (((u * c : ℝ) : ℂ) * Complex.I) =
              Complex.exp (((u * m : ℝ) : ℂ) * Complex.I) * ((ψ (u ^ 2 * v) : ℝ) : ℂ) := by
            intro u
            rw [← hline u]
            have h : ∫ x, Complex.exp (((u * ∑ j, x j : ℝ) : ℂ) * Complex.I) ∂P =
                ∫ _x, Complex.exp (((u * c : ℝ) : ℂ) * Complex.I) ∂P := by
              apply integral_congr_ae
              filter_upwards [hc] with x hx
              rw [hx]
            rw [h]
            simp
          have hdiff : ∀ u : ℝ, Complex.exp (((u * (c - m) : ℝ) : ℂ) * Complex.I) =
              ((ψ (u ^ 2 * v) : ℝ) : ℂ) := by
            intro u
            have h := hexp u
            have h2 : Complex.exp (((u * c : ℝ) : ℂ) * Complex.I) =
                Complex.exp (((u * m : ℝ) : ℂ) * Complex.I) *
                  Complex.exp (((u * (c - m) : ℝ) : ℂ) * Complex.I) := by
              rw [← Complex.exp_add]
              congr 1
              push_cast
              ring
            rw [h2] at h
            exact mul_left_cancel₀ (Complex.exp_ne_zero _) h
          have hcm : c - m = 0 := by
            by_contra hne
            have h := congrArg Complex.im (hdiff (Real.pi / 2 / (c - m)))
            rw [div_mul_cancel₀ _ hne, Complex.exp_ofReal_mul_I_im, Complex.ofReal_im,
              Real.sin_pi_div_two] at h
            exact one_ne_zero h
          have hone : ∀ u : ℝ, ψ (u ^ 2 * v) = 1 := by
            intro u
            have h := hdiff u
            rw [hcm] at h
            have h2 : (1 : ℂ) = ((ψ (u ^ 2 * v) : ℝ) : ℂ) := by simpa using h
            exact_mod_cast h2.symm
          by_cases hvz : v = 0
          · exact Or.inl hvz
          · right
            intro s hs
            have h := hone (Real.sqrt (s / v))
            rwa [Real.sq_sqrt (div_nonneg hs hv0), div_mul_cancel₀ _ hvz] at h
        · intro hor
          have hone : ∀ u : ℝ, ψ (u ^ 2 * v) = 1 := by
            intro u
            rcases hor with h | h
            · rw [h, mul_zero, hψ0]
            · exact h _ (mul_nonneg (sq_nonneg u) hv0)
          refine ⟨m, ?_⟩
          have : IsProbabilityMeasure (P.map (fun x : Fin n → ℝ => ∑ i, x i)) :=
            Measure.isProbabilityMeasure_map hmeas.aemeasurable
          have hQ : P.map (fun x : Fin n → ℝ => ∑ i, x i) = Measure.dirac m := by
            apply Measure.ext_of_charFun
            funext u
            rw [charFun_apply_real, charFun_apply_real, integral_dirac,
              integral_map hmeas.aemeasurable (by fun_prop)]
            have h := hline u
            rw [hone u] at h
            push_cast at h ⊢
            simpa using h
          have hae : ∀ᵐ y ∂(P.map (fun x : Fin n → ℝ => ∑ i, x i)), y = m := by
            rw [hQ]
            exact (ae_dirac_iff (p := fun y : ℝ => y = m) (measurableSet_singleton m)).2 rfl
          exact ae_of_ae_map hmeas.aemeasurable hae
