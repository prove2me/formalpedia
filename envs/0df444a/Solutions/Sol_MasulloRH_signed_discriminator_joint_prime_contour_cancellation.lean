-- Prove2me | solution 1 for MasulloRH.signed_discriminator_joint_prime_contour_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T08:20:19.500988+00:00
-- url     : https://prove2.me/submissions/a9cc3779-05c3-4eed-8140-2a62bdca3da9

import Mathlib
import Definitions.Def_Zeta23_WeilEF_VerticalLine
import Theorems.Thm_MasulloRH_exists_positive_log_profile_rank_discriminator
import Theorems.Thm_MasulloRH_translated_half_weight_prime_power_sum_and_nonvanishing
import Theorems.Thm_MasulloRH_actual_translated_zeta_contour_pole_limit
open Filter Topology Complex MeasureTheory Zeta23 Zeta23.WeilEF Set
private theorem zexp_sub (g : ℝ → ℂ) :
    ∫ x : ℝ, Real.exp x • g (Real.exp x) = ∫ y in Ioi (0:ℝ), g y := by
  symm
  rw [← Real.range_exp, ← Set.image_univ]
  simpa using integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g
private noncomputable def zj (u : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, u (Real.exp x) * Real.exp (x/2)
private theorem zcast (u : ℝ → ℝ) : (∫ x : ℝ, ((u (Real.exp x) * Real.exp (x/2) : ℝ) : ℂ)) = (zj u : ℂ) :=
  integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure ℝ)) (f := fun x : ℝ => u (Real.exp x) * Real.exp (x/2))
private theorem zmell (u : ℝ → ℝ) :
    mellin (fun t => (u t:ℂ)) (1/2:ℂ) = (zj u : ℂ) := by
  rw [mellin, ← zexp_sub]
  refine Eq.trans ?_ (zcast u)
  apply integral_congr_ae
  filter_upwards [] with x
  have hpos : 0 < Real.exp x := Real.exp_pos _
  rw [Complex.real_smul, smul_eq_mul]
  change (Real.exp x : ℂ) * (((Real.exp x : ℂ)) ^ ((1/2:ℂ)-1) * (u (Real.exp x):ℂ)) = _
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hpos.ne'), ← Complex.ofReal_log hpos.le, Real.log_exp]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  have he : (x:ℂ)+(x:ℂ)*((1/2:ℂ)-1)=(x:ℂ)/2 := by ring
  rw [he]; ring
private theorem zhfn (u : ℝ → ℝ) :
    Hfn (fun x => (u (Real.exp x):ℂ)) 1 = (zj u : ℂ) := by
  unfold Hfn paperFT
  refine Eq.trans ?_ (zcast u)
  apply integral_congr_ae
  filter_upwards [] with x
  have he : I * (((1:ℂ)-1/2)/I) = 1/2 := by field_simp; ring
  rw [he]
  push_cast
  rw [show (1/2:ℂ) * (x:ℂ) = (x:ℂ)/2 from by ring]
theorem solution :
    ∃ u : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ tsupport u ⊆ Ioo 1 32 ∧
      HasMellin (fun t => (u t:ℂ)) 1 0 ∧ HasMellin (fun t => (u t:ℂ)) (-(1/2):ℂ) 0 ∧
      0 < (mellin (fun t => (u t:ℂ)) (1/2:ℂ)).re ∧
      ∀ c : ℝ, 1 < c → c ≤ 3/2 →
      let P := fun L : ℝ =>
        (∑ n ∈ Finset.Ioc ⌊Real.exp L⌋₊ ⌊32*Real.exp L⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n * u ((n:ℝ)/Real.exp L)) / Real.sqrt (Real.exp L)
      let C := fun L : ℝ =>
        let f := fun x : ℝ => Complex.exp (-(L:ℂ)/2) * (u (Real.exp (x-L)):ℂ)
        (1/(2*Real.pi):ℂ) * ∫ t : ℝ,
          (Hfn f ((c:ℂ)+t*I) + Hfn f (1-c-t*I)) * logDeriv completedRiemannZeta ((c:ℂ)+t*I)
      Tendsto P atTop (𝓝 (mellin (fun t => (u t:ℂ)) (1/2:ℂ)).re) ∧
      Tendsto (fun L => (P L:ℂ) + C L) atTop (𝓝 0) := by
  obtain ⟨u,hu,hcs,ht,h1,hn,hm,hlog⟩ := MasulloRH.exists_positive_log_profile_rank_discriminator
  refine ⟨u,hu,hcs,ht,h1,hn,hm,?_⟩
  intro c hc1 hc2 P C
  have hpa := MasulloRH.translated_half_weight_prime_power_sum_and_nonvanishing.1 1 32 (by norm_num) (by norm_num) u
    (hu.of_le (by simp)) ht
  have hp : Tendsto P atTop (𝓝 (mellin (fun t => (u t:ℂ)) (1/2:ℂ)).re) := by
    simpa only [P,Function.comp_def,one_mul] using hpa.comp Real.tendsto_exp_atTop
  refine ⟨hp,?_⟩
  let k := fun x : ℝ => (u (Real.exp x):ℂ)
  have hk : ContDiff ℝ 2 k := by
    have hu2 : ContDiff ℝ 2 u := hu.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞) ≤ ⊤))
    exact Complex.ofRealCLM.contDiff.comp (hu2.comp Real.contDiff_exp)
  have hkc : HasCompactSupport k := by
    exact hlog.2.1.comp_left Complex.ofReal_zero
  have hcl : Tendsto C atTop (𝓝 (-Hfn k 1)) :=
    MasulloRH.actual_translated_zeta_contour_pole_limit k hk hkc hc1 hc2
  have htend := ((Complex.continuous_ofReal.tendsto _).comp hp).add hcl
  rw [zmell,Complex.ofReal_re,show Hfn k 1 = (zj u:ℂ) from zhfn u,add_neg_cancel] at htend
  exact htend
