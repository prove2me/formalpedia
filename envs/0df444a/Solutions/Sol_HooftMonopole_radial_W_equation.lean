-- Prove2me | solution 1 for HooftMonopole.radial_W_equation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:39:36.556669+00:00
-- url     : https://prove2.me/submissions/ad2e1e54-07dd-4255-815f-5276e1075f07

import Mathlib
import Definitions.Def_HooftMonopole_Defs

open MeasureTheory Filter Topology Real

namespace HooftMonopole

noncomputable def aux_hw_V (j : Fin 3) : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => ∑ a, (∑ b, levi j a b * y b) • EuclideanSpace.single a (1:ℝ)
      map_add' := by
        intro y z; ext c; fin_cases c <;> simp [Fin.sum_univ_three] <;> ring
      map_smul' := by
        intro m y; ext c; fin_cases c <;> simp [Fin.sum_univ_three] <;> ring }

lemma aux_hw_V_apply (j : Fin 3) (y : Space) :
    aux_hw_V j y = ∑ a, (∑ b, levi j a b * y b) • EuclideanSpace.single a (1:ℝ) := rfl

lemma aux_hw_gauge_eq (w : ℝ → ℝ) (j : Fin 3) :
    hedgehogGauge w j = fun y => w ‖y‖ • aux_hw_V j y := rfl

lemma aux_hw_higgs_eq (q : ℝ → ℝ) :
    hedgehogHiggs q = fun y => q ‖y‖ • (ContinuousLinearMap.id ℝ Space) y := rfl

lemma aux_hw_norm_hasFDerivAt (x : Space) (hx : x ≠ 0) :
    HasFDerivAt (fun y : Space => ‖y‖) ((1 / (2 * √(‖x‖ ^ 2))) • (2 • innerSL ℝ x)) x := by
  have hx' : ‖x‖ ^ 2 ≠ 0 := by positivity
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt hx'
  have he : (fun y : Space => √(‖y‖ ^ 2)) = fun y => ‖y‖ := by
    funext y; rw [Real.sqrt_sq (norm_nonneg y)]
  rw [he] at h
  exact h

lemma aux_hw_pd (φ : ℝ → ℝ) (L : Space →L[ℝ] Space) (x : Space) (hx : x ≠ 0)
    (hφ : DifferentiableAt ℝ φ ‖x‖) (i a : Fin 3) :
    partialDeriv (fun y => φ ‖y‖ • L y) i x a
      = φ ‖x‖ * L (EuclideanSpace.single i 1) a + deriv φ ‖x‖ / ‖x‖ * x i * L x a := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hn := aux_hw_norm_hasFDerivAt x hx
  have hc := hφ.hasDerivAt.comp_hasFDerivAt x hn
  have h : HasFDerivAt (fun y => φ ‖y‖ • L y) _ x := hc.smul L.hasFDerivAt
  unfold partialDeriv
  rw [h.fderiv]
  simp [EuclideanSpace.inner_single_right, Real.sqrt_sq hr.le]
  left
  field_simp


lemma aux_hw_density (e lam F : ℝ) (q w : ℝ → ℝ) (x : Space) (hx : x ≠ 0)
    (hq : DifferentiableAt ℝ q ‖x‖) (hw : DifferentiableAt ℝ w ‖x‖) :
    energyDensity e lam F (hedgehogHiggs q) (hedgehogGauge w) x
      = radialEnergyIntegrand e lam F w q ‖x‖ := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hs : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have hQ : ∀ i a, partialDeriv (hedgehogHiggs q) i x a
      = q ‖x‖ * (EuclideanSpace.single i (1:ℝ)) a + deriv q ‖x‖ / ‖x‖ * x i * x a := by
    intro i a
    rw [aux_hw_higgs_eq]
    exact aux_hw_pd q _ x hx hq i a
  have hW : ∀ j i a, partialDeriv (hedgehogGauge w j) i x a
      = w ‖x‖ * aux_hw_V j (EuclideanSpace.single i 1) a
        + deriv w ‖x‖ / ‖x‖ * x i * aux_hw_V j x a := by
    intro j i a
    rw [aux_hw_gauge_eq]
    exact aux_hw_pd w _ x hx hw i a
  set om := deriv w ‖x‖ / ‖x‖ with hom_def
  set p := deriv q ‖x‖ / ‖x‖ with hp_def
  have hom : deriv w ‖x‖ = om * ‖x‖ := by rw [hom_def]; field_simp
  have hp : deriv q ‖x‖ = p * ‖x‖ := by rw [hp_def]; field_simp
  clear_value om p
  unfold energyDensity fieldStrength covDeriv higgsNormSq radialEnergyIntegrand
  simp only [hQ, hW]
  rw [hom, hp]
  simp [aux_hw_V_apply, hedgehogGauge, hedgehogHiggs, Fin.sum_univ_three, levi]
  norm_num
  generalize ‖x‖ = r at hs ⊢
  generalize w r = W
  generalize q r = Q
  generalize x 0 = x0 at hs ⊢
  generalize x 1 = x1 at hs ⊢
  generalize x 2 = x2 at hs ⊢
  linear_combination (-2*F^2*Q^2*lam + Q^4*lam*r^2 + Q^4*lam*(x0^2+x1^2+x2^2) + 8*Q^2*W^2*e^2*r^2
    + 8*Q^2*W^2*e^2*(x0^2+x1^2+x2^2) + 16*Q^2*W*e + 8*Q*p + 4*W^4*e^2*r^2
    + 4*W^4*e^2*(x0^2+x1^2+x2^2) + 16*W^3*e + 32*W*om + 8*om^2*r^2 + 8*om^2*(x0^2+x1^2+x2^2)
    + 4*p^2*r^2 + 4*p^2*(x0^2+x1^2+x2^2))/8 * hs


lemma aux_hw_reg (f : ℝ → ℝ) (G : Space → Space) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (v : Space)
    (a : Fin 3) (h : ∀ s : ℝ, 0 < s → G (s • v) a = f s * s) :
    ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioi 0) := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => G (s • v)) :=
    hG.comp (contDiff_id.smul contDiff_const)
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => G (s • v) a) :=
    (EuclideanSpace.proj a : Space →L[ℝ] ℝ).contDiff.comp h0
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => G (s • v) a / s) (Set.Ioi 0) :=
    h1.contDiffOn.div contDiffOn_id (fun s hs => ne_of_gt hs)
  refine h2.congr (fun s hs => ?_)
  have hs' : (0:ℝ) < s := hs
  rw [h s hs']
  field_simp

lemma aux_hw_reg_q (q : ℝ → ℝ) (hQ : ContDiff ℝ (⊤ : ℕ∞) (hedgehogHiggs q)) :
    ContDiffOn ℝ (⊤ : ℕ∞) q (Set.Ioi 0) := by
  refine aux_hw_reg q _ hQ (EuclideanSpace.single 0 1) 0 (fun s hs => ?_)
  simp [hedgehogHiggs, norm_smul, abs_of_pos hs]

lemma aux_hw_reg_w (w : ℝ → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) (hedgehogGauge w 0)) :
    ContDiffOn ℝ (⊤ : ℕ∞) w (Set.Ioi 0) := by
  refine aux_hw_reg w _ hW (EuclideanSpace.single 2 1) 1 (fun s hs => ?_)
  simp [hedgehogGauge, norm_smul, abs_of_pos hs, Fin.sum_univ_three, levi]
  norm_num

lemma aux_hw_ae_ne : ∀ᵐ x ∂(volume : Measure Space), x ≠ 0 := by
  rw [ae_iff]
  simp

lemma aux_hw_ae_density (e lam F : ℝ) (q w : ℝ → ℝ) (hq : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ q y)
    (hw : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ w y) :
    energyDensity e lam F (hedgehogHiggs q) (hedgehogGauge w)
      =ᵐ[volume] fun x => radialEnergyIntegrand e lam F w q ‖x‖ := by
  filter_upwards [aux_hw_ae_ne] with x hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  exact aux_hw_density e lam F q w x hx (hq _ hr) (hw _ hr)

lemma aux_hw_energy_eq (e lam F : ℝ) (q w : ℝ → ℝ) (hq : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ q y)
    (hw : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ w y) :
    energy e lam F (hedgehogHiggs q) (hedgehogGauge w)
      = (3 * (volume : Measure Space).real (Metric.ball 0 1)) *
          ∫ y in Set.Ioi (0:ℝ), y ^ 2 * radialEnergyIntegrand e lam F w q y := by
  unfold energy
  rw [integral_congr_ae (aux_hw_ae_density e lam F q w hq hw)]
  rw [integral_fun_norm_addHaar (volume : Measure Space)
    (fun y => radialEnergyIntegrand e lam F w q y)]
  simp [nsmul_eq_mul, smul_eq_mul, mul_assoc]

lemma aux_hw_intOn (e lam F : ℝ) (q w : ℝ → ℝ) (hq : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ q y)
    (hw : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ w y)
    (hint : Integrable (energyDensity e lam F (hedgehogHiggs q) (hedgehogGauge w))) :
    IntegrableOn (fun y => y ^ 2 * radialEnergyIntegrand e lam F w q y) (Set.Ioi 0) := by
  have h1 := hint.congr (aux_hw_ae_density e lam F q w hq hw)
  have h2 := (integrable_fun_norm_addHaar (volume : Measure Space)
    (f := fun y => radialEnergyIntegrand e lam F w q y)).mp h1
  simpa [finrank_euclideanSpace_fin, smul_eq_mul] using h2


noncomputable def aux_hw_P (e : ℝ) (w q : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * (4 * s * deriv w s + 12 * w s + 6 * e * s ^ 2 * w s ^ 2
      + 2 * e ^ 2 * s ^ 4 * w s ^ 3 + 2 * e * s ^ 2 * q s ^ 2 + 2 * e ^ 2 * s ^ 4 * w s * q s ^ 2)

noncomputable def aux_hw_M (w : ℝ → ℝ) (s : ℝ) : ℝ := 2 * s ^ 4 * deriv w s + 4 * s ^ 3 * w s

noncomputable def aux_hw_B (e : ℝ) (w q g : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * (s ^ 2 * deriv g s ^ 2 + 4 * s * g s * deriv g s + 6 * g s ^ 2
    + 6 * e * s ^ 2 * w s * g s ^ 2 + 3 * e ^ 2 * s ^ 4 * w s ^ 2 * g s ^ 2
    + e ^ 2 * s ^ 4 * q s ^ 2 * g s ^ 2)

noncomputable def aux_hw_C (e : ℝ) (w g : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * (2 * e * s ^ 2 * g s ^ 3 + 2 * e ^ 2 * s ^ 4 * w s * g s ^ 3)

noncomputable def aux_hw_D (e : ℝ) (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * (1 / 2 * e ^ 2 * s ^ 4 * g s ^ 4)

lemma aux_hw_expand (e lam F t y : ℝ) (q w g : ℝ → ℝ) (hw : DifferentiableAt ℝ w y)
    (hg : DifferentiableAt ℝ g y) :
    y ^ 2 * radialEnergyIntegrand e lam F (fun s => w s + t * g s) q y
      = y ^ 2 * radialEnergyIntegrand e lam F w q y
        + (t * (g y * aux_hw_P e w q y + deriv g y * aux_hw_M w y) + t ^ 2 * aux_hw_B e w q g y
          + t ^ 3 * aux_hw_C e w g y + t ^ 4 * aux_hw_D e g y) := by
  have hd : deriv (fun s => w s + t * g s) y = deriv w y + t * deriv g y := by
    have h1 : HasDerivAt (fun s => w s + t * g s) (deriv w y + t * deriv g y) y :=
      hw.hasDerivAt.add (hg.hasDerivAt.const_mul t)
    exact h1.deriv
  unfold radialEnergyIntegrand aux_hw_P aux_hw_M aux_hw_B aux_hw_C aux_hw_D
  rw [hd]
  ring

lemma aux_hw_dg_zero (g : ℝ → ℝ) (y : ℝ) (hy : y ∉ tsupport g) : deriv g y = 0 := by
  have : y ∉ Function.support (deriv g) := fun h => hy (support_deriv_subset h)
  simpa using this

lemma aux_hw_gnorm_contDiff (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : tsupport g ⊆ Set.Ioi 0) : ContDiff ℝ (⊤ : ℕ∞) (fun y : Space => g ‖y‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have h0 : (0:ℝ) ∉ tsupport g := fun h => lt_irrefl (0:ℝ) (hgs h)
    have hev : g =ᶠ[𝓝 0] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp h0
    have hc : Filter.Tendsto (fun y : Space => ‖y‖) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0:Space))
    have hev2 : (fun y : Space => g ‖y‖) =ᶠ[𝓝 0] fun _ => 0 := hc.eventually hev
    exact contDiffAt_const.congr_of_eventuallyEq hev2
  · exact hg.contDiffAt.comp x (contDiffAt_norm ℝ hx)

lemma aux_hw_gnorm_compact (g : ℝ → ℝ) (hgc : HasCompactSupport g) :
    HasCompactSupport (fun y : Space => g ‖y‖) := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0:Space) R) (fun y hy => ?_)
  apply image_eq_zero_of_notMem_tsupport
  intro h
  apply hy
  have := hR h
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)] using this

lemma aux_hw_dW_contDiff (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : tsupport g ⊆ Set.Ioi 0) (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (hedgehogGauge g i) := by
  rw [aux_hw_gauge_eq]
  exact (aux_hw_gnorm_contDiff g hg hgs).smul (aux_hw_V i).contDiff

lemma aux_hw_dW_compact (g : ℝ → ℝ) (hgc : HasCompactSupport g) (i : Fin 3) :
    HasCompactSupport (hedgehogGauge g i) := by
  rw [aux_hw_gauge_eq]
  exact HasCompactSupport.smul_right (f := fun y : Space => g ‖y‖) (aux_hw_gnorm_compact g hgc)

lemma aux_hw_int_of (φ : ℝ → ℝ) (K : Set ℝ) (hK : IsCompact K) (hKs : K ⊆ Set.Ioi 0)
    (hφ : ContinuousOn φ (Set.Ioi 0)) (h0 : ∀ y, y ∉ K → φ y = 0) : Integrable φ := by
  have h1 : IntegrableOn φ K := (hφ.mono hKs).integrableOn_compact hK
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
  intro y hy
  by_contra h
  exact hy (h0 y h)

lemma aux_hw_int_interval (φ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (h0 : ∀ y, y ∉ Set.Ioo a b → φ y = 0) : ∫ y, φ y = ∫ y in a..b, φ y := by
  rw [intervalIntegral.integral_of_le hab, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro y hy
  apply h0
  intro h
  exact hy (Set.Ioo_subset_Ioc_self h)

lemma aux_hw_weak (e lam F : ℝ) (q w : ℝ → ℝ)
    (hsol : IsStaticSolution e lam F (hedgehogHiggs q) (hedgehogGauge w))
    (hqc : ContinuousOn q (Set.Ioi 0)) (hwc : ContinuousOn w (Set.Ioi 0))
    (hqd : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ q y)
    (hwd : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ w y)
    (hPc : ContinuousOn (aux_hw_P e w q) (Set.Ioi 0))
    (hMc : ContinuousOn (aux_hw_M w) (Set.Ioi 0))
    (hMd : ∀ y : ℝ, 0 < y → HasDerivAt (aux_hw_M w) (deriv (aux_hw_M w) y) y)
    (hdMc : ContinuousOn (deriv (aux_hw_M w)) (Set.Ioi 0))
    (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ Set.Ioi 0) :
    ∫ y, g y • (aux_hw_P e w q y - deriv (aux_hw_M w) y) = 0 := by
  obtain ⟨_, _, hint, hvar⟩ := hsol
  have hgd : ∀ y, DifferentiableAt ℝ g y := fun y => (hg.differentiable (by simp)) y
  have hgcont : Continuous g := hg.continuous
  have hdgcont : Continuous (deriv g) := hg.continuous_deriv (by simp)
  have hg0 : ∀ y, y ∉ tsupport g → g y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hdg0 : ∀ y, y ∉ tsupport g → deriv g y = 0 := fun y hy => aux_hw_dg_zero g y hy
  have hK : IsCompact (tsupport g) := hgc
  -- the variation
  have hvar' := hvar 0 (hedgehogGauge g) contDiff_const HasCompactSupport.zero
    (fun i => aux_hw_dW_contDiff g hg hgs i) (fun i => aux_hw_dW_compact g hgc i)
  have hfun : (fun t : ℝ => energy e lam F (fun x => hedgehogHiggs q x + t • (0 : Space → Space) x)
      (fun i x => hedgehogGauge w i x + t • hedgehogGauge g i x))
      = fun t => energy e lam F (hedgehogHiggs q) (hedgehogGauge (fun s => w s + t * g s)) := by
    funext t
    congr 1
    · funext x
      simp
    · funext i x
      simp only [hedgehogGauge]
      rw [add_smul, mul_smul]
  rw [hfun] at hvar'
  -- integrability of the pieces
  set a1 : ℝ → ℝ := fun y => g y * aux_hw_P e w q y + deriv g y * aux_hw_M w y with ha1
  have i1 : Integrable a1 := by
    refine aux_hw_int_of a1 _ hK hgs ?_ (fun y hy => by simp [a1, hg0 y hy, hdg0 y hy])
    exact (hgcont.continuousOn.mul hPc).add (hdgcont.continuousOn.mul hMc)
  have i2 : Integrable (aux_hw_B e w q g) := by
    refine aux_hw_int_of _ _ hK hgs ?_ (fun y hy => by simp [aux_hw_B, hg0 y hy, hdg0 y hy])
    have := hgcont.continuousOn (s := Set.Ioi 0)
    have := hdgcont.continuousOn (s := Set.Ioi 0)
    unfold aux_hw_B
    fun_prop
  have i3 : Integrable (aux_hw_C e w g) := by
    refine aux_hw_int_of _ _ hK hgs ?_ (fun y hy => by simp [aux_hw_C, hg0 y hy])
    have := hgcont.continuousOn (s := Set.Ioi 0)
    unfold aux_hw_C
    fun_prop
  have i4 : Integrable (aux_hw_D e g) := by
    refine aux_hw_int_of _ _ hK hgs ?_ (fun y hy => by simp [aux_hw_D, hg0 y hy])
    have := hgcont.continuousOn (s := Set.Ioi 0)
    unfold aux_hw_D
    fun_prop
  have i0 := aux_hw_intOn e lam F q w hqd hwd hint
  set c : ℝ := 3 * (volume : Measure Space).real (Metric.ball 0 1) with hc
  set I0 := ∫ y in Set.Ioi (0:ℝ), y ^ 2 * radialEnergyIntegrand e lam F w q y
  set I1 := ∫ y in Set.Ioi (0:ℝ), a1 y
  set I2 := ∫ y in Set.Ioi (0:ℝ), aux_hw_B e w q g y
  set I3 := ∫ y in Set.Ioi (0:ℝ), aux_hw_C e w g y
  set I4 := ∫ y in Set.Ioi (0:ℝ), aux_hw_D e g y
  have hE : ∀ t : ℝ, energy e lam F (hedgehogHiggs q) (hedgehogGauge (fun s => w s + t * g s))
      = c * (I0 + (t * I1 + t ^ 2 * I2 + t ^ 3 * I3 + t ^ 4 * I4)) := by
    intro t
    have hd : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ (fun s => w s + t * g s) y :=
      fun y hy => (hwd y hy).add ((hgd y).const_mul t)
    rw [aux_hw_energy_eq e lam F q (fun s => w s + t * g s) hqd hd]
    congr 1
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun y hy => aux_hw_expand e lam F t y q w g (hwd y hy) (hgd y))]
    have j1 := (i1.const_mul t).integrableOn (s := Set.Ioi (0:ℝ))
    have j2 := (i2.const_mul (t ^ 2)).integrableOn (s := Set.Ioi (0:ℝ))
    have j3 := (i3.const_mul (t ^ 3)).integrableOn (s := Set.Ioi (0:ℝ))
    have j4 := (i4.const_mul (t ^ 4)).integrableOn (s := Set.Ioi (0:ℝ))
    have j12 : IntegrableOn (fun y => t * a1 y + t ^ 2 * aux_hw_B e w q g y) (Set.Ioi 0) :=
      j1.add j2
    have j123 : IntegrableOn (fun y => t * a1 y + t ^ 2 * aux_hw_B e w q g y
        + t ^ 3 * aux_hw_C e w g y) (Set.Ioi 0) := j12.add j3
    have j1234 : IntegrableOn (fun y => t * a1 y + t ^ 2 * aux_hw_B e w q g y
        + t ^ 3 * aux_hw_C e w g y + t ^ 4 * aux_hw_D e g y) (Set.Ioi 0) := j123.add j4
    show ∫ y in Set.Ioi (0:ℝ), (y ^ 2 * radialEnergyIntegrand e lam F w q y
      + (t * a1 y + t ^ 2 * aux_hw_B e w q g y + t ^ 3 * aux_hw_C e w g y
        + t ^ 4 * aux_hw_D e g y)) = _
    rw [integral_add i0 j1234]
    rw [integral_add j123 j4, integral_add j12 j3, integral_add j1 j2]
    rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hfun2 : (fun t : ℝ => energy e lam F (hedgehogHiggs q)
      (hedgehogGauge (fun s => w s + t * g s)))
      = fun t => c * (I0 + (t * I1 + t ^ 2 * I2 + t ^ 3 * I3 + t ^ 4 * I4)) := funext hE
  rw [hfun2] at hvar'
  have hpoly : HasDerivAt (fun t : ℝ => c * (I0 + (t * I1 + t ^ 2 * I2 + t ^ 3 * I3 + t ^ 4 * I4)))
      (c * I1) 0 := by
    have h := (((((hasDerivAt_id' (0:ℝ)).mul_const I1).add
      ((hasDerivAt_pow 2 (0:ℝ)).mul_const I2)).add
      ((hasDerivAt_pow 3 (0:ℝ)).mul_const I3)).add
      ((hasDerivAt_pow 4 (0:ℝ)).mul_const I4)).const_add I0 |>.const_mul c
    exact h.congr_deriv (by simp)
  have hcpos : 0 < c := by
    rw [hc]
    have h1 : 0 < (volume : Measure Space) (Metric.ball 0 1) := Metric.measure_ball_pos _ _ one_pos
    have h2 : (volume : Measure Space) (Metric.ball 0 1) < ⊤ := measure_ball_lt_top
    have : 0 < (volume : Measure Space).real (Metric.ball 0 1) :=
      ENNReal.toReal_pos h1.ne' h2.ne
    positivity
  have hI1 : I1 = 0 := by
    have := hvar'.unique hpoly
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hcpos.ne'
    · exact h
  -- choose an interval containing the support
  obtain ⟨a, b, ha, hab, hKab⟩ : ∃ a b : ℝ, 0 < a ∧ a < b ∧ tsupport g ⊆ Set.Ioo a b := by
    rcases (tsupport g).eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, 2, one_pos, one_lt_two, by simp [hKe]⟩
    · obtain ⟨m, hmK, hm⟩ := hK.exists_isMinOn hKne continuousOn_id
      obtain ⟨B, hB⟩ := hK.bddAbove
      have hm0 : 0 < m := hgs hmK
      refine ⟨m / 2, max B m + 1, by positivity, ?_, ?_⟩
      · have := le_max_right B m
        linarith
      · intro y hy
        have h1 : m ≤ y := by simpa using hm hy
        have h2 : y ≤ B := hB hy
        constructor
        · linarith
        · have := le_max_left B m
          linarith
  have hsub : Set.uIcc a b ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le hab.le]
    intro y hy
    exact lt_of_lt_of_le ha hy.1
  have hga : g a = 0 := hg0 a (fun h => lt_irrefl a (hKab h).1)
  have hgb : g b = 0 := hg0 b (fun h => lt_irrefl b (hKab h).2)
  have hout : ∀ y, y ∉ Set.Ioo a b → y ∉ tsupport g := fun y hy h => hy (hKab h)
  -- FTC for g * M
  have hftc : ∫ y in a..b, (deriv g y * aux_hw_M w y + g y * deriv (aux_hw_M w) y) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => g y * aux_hw_M w y)]
    · simp [hga, hgb]
    · intro y hy
      exact (hgd y).hasDerivAt.mul (hMd y (hsub hy))
    · apply ContinuousOn.intervalIntegrable
      exact ((hdgcont.continuousOn.mul hMc).add (hgcont.continuousOn.mul hdMc)).mono hsub
  have hI1' : I1 = ∫ y in a..b, a1 y := by
    rw [← aux_hw_int_interval a1 a b hab.le (fun y hy => by simp [a1, hg0 y (hout y hy), hdg0 y (hout y hy)])]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have : y ∉ tsupport g := fun h => hy (hgs h)
    simp [a1, hg0 y this, hdg0 y this]
  rw [aux_hw_int_interval _ a b hab.le (fun y hy => by simp [hg0 y (hout y hy)])]
  have hint1 : IntervalIntegrable a1 volume a b := i1.intervalIntegrable
  have hint2 : IntervalIntegrable (fun y => deriv g y * aux_hw_M w y + g y * deriv (aux_hw_M w) y)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact ((hdgcont.continuousOn.mul hMc).add (hgcont.continuousOn.mul hdMc)).mono hsub
  have heq : (fun y => g y • (aux_hw_P e w q y - deriv (aux_hw_M w) y))
      = fun y => a1 y - (deriv g y * aux_hw_M w y + g y * deriv (aux_hw_M w) y) := by
    funext y
    simp only [a1, smul_eq_mul]
    ring
  rw [heq, intervalIntegral.integral_sub hint1 hint2, hftc, ← hI1', hI1]
  simp

end HooftMonopole

open HooftMonopole

theorem solution (e lam F : ℝ) (q w : ℝ → ℝ)
    (hsol : IsStaticSolution e lam F (hedgehogHiggs q) (hedgehogGauge w)) :
    ∀ r : ℝ, 0 < r → radialWEquation e w q r := by
  have hq := aux_hw_reg_q q hsol.1
  have hw := aux_hw_reg_w w (hsol.2.1 0)
  have hqc : ContinuousOn q (Set.Ioi 0) := hq.continuousOn
  have hwc : ContinuousOn w (Set.Ioi 0) := hw.continuousOn
  have hw' : ContDiffOn ℝ (⊤ : ℕ∞) (deriv w) (Set.Ioi 0) :=
    hw.deriv_of_isOpen isOpen_Ioi (by simp)
  have hw'c : ContinuousOn (deriv w) (Set.Ioi 0) := hw'.continuousOn
  have hqd : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ q y := fun y hy =>
    (hq.contDiffAt (Ioi_mem_nhds hy)).differentiableAt (by simp)
  have hwd : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ w y := fun y hy =>
    (hw.contDiffAt (Ioi_mem_nhds hy)).differentiableAt (by simp)
  have hPc : ContinuousOn (aux_hw_P e w q) (Set.Ioi 0) := by
    unfold aux_hw_P
    fun_prop
  have hMc' : ContDiffOn ℝ (⊤ : ℕ∞) (aux_hw_M w) (Set.Ioi 0) := by
    unfold aux_hw_M
    fun_prop
  have hMc : ContinuousOn (aux_hw_M w) (Set.Ioi 0) := hMc'.continuousOn
  have hMd : ∀ y : ℝ, 0 < y → HasDerivAt (aux_hw_M w) (deriv (aux_hw_M w) y) y := fun y hy =>
    ((hMc'.contDiffAt (Ioi_mem_nhds hy)).differentiableAt (by simp)).hasDerivAt
  have hdMc : ContinuousOn (deriv (aux_hw_M w)) (Set.Ioi 0) :=
    (hMc'.deriv_of_isOpen isOpen_Ioi (m := (⊤ : ℕ∞)) (by simp)).continuousOn
  have hcont : ContinuousOn (fun y => aux_hw_P e w q y - deriv (aux_hw_M w) y) (Set.Ioi 0) :=
    hPc.sub hdMc
  have hae := (isOpen_Ioi (a := (0:ℝ))).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hcont.locallyIntegrableOn measurableSet_Ioi)
    (fun g hg hgc hgs => aux_hw_weak e lam F q w hsol hqc hwc hqd hwd hPc hMc hMd hdMc
      g hg hgc hgs)
  have heq : Set.EqOn (fun y => aux_hw_P e w q y - deriv (aux_hw_M w) y) (fun _ => 0)
      (Set.Ioi 0) := by
    apply Measure.eqOn_open_of_ae_eq (μ := (volume : Measure ℝ)) _ isOpen_Ioi hcont
      continuousOn_const
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae] with y hy hy'
    exact hy hy'
  intro r hr
  have h1 := heq (show r ∈ Set.Ioi 0 from hr)
  simp only at h1
  unfold radialWEquation
  have h2 : deriv (aux_hw_M w) r = aux_hw_P e w q r := by linarith
  exact h2
