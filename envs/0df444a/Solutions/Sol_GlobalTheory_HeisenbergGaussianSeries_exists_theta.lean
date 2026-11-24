-- Prove2me | solution 1 for GlobalTheory.HeisenbergGaussianSeries.exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:59:14.979466+00:00
-- url     : https://prove2.me/submissions/c838fbcc-c5d8-4cf6-9bc5-7a0b4258d150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExpSeriesContDiffAndHasDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CharSeriesExistsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosMulNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousBicharacterWeilSetup
import Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_exists_exponent
import Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_contDiff_bilin
import Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_summable_coeff
import Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_series_quasi
import Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_series_inv
import Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_series_expand
import Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_series_neg
import Theorems.Thm_GlobalTheory_charSeries_exists_ne_zero
import Theorems.Thm_GlobalTheory_expSeries_contDiff_and_hasDerivAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.HeisenbergGaussianSeries
namespace GlobalTheory.HeisenbergGaussianSeries
theorem _root_.solution : ∀ (G V : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : G →+ V) (ι : V →+ G) (β : G → G → ℂ) (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) (Γ U₀ U : AddSubgroup G) (χ : G → ℂ), Continuous p → Continuous ι → (∀ v, p (ι v) = v) → (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y z, β x (y + z) = β x y * β x z) → (∀ x, β x x = 1) → (∀ x y, ‖β x y‖ = 1) → Continuous (fun q : G × G => β q.1 q.2) → (∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ))) → (∀ v, om v v = 0) → (∀ v, J (J v) = -v) → (∀ x y, om x (J y) = om y (J x)) → (∀ v, v ≠ 0 → 0 < om v (J v)) → (∀ g ∈ Γ, ∀ g' ∈ Γ, β g g' = 1) → (∀ g ∈ Γ, p g = 0 → g = 0) → (∀ v, ι v ∈ U₀) → (∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U₀ ∧ ‖p g‖ ≤ R}.Finite) → (∀ x, x ∉ U₀ → χ x = 0) → (∀ x, ‖χ x‖ ≤ 1) → χ 0 = 1 → (∀ x v, χ (x + ι v) = χ x) → IsOpen (U : Set G) → (∀ u ∈ U, ∀ x, β x (u - ι (p u)) * χ (x + (u - ι (p u))) = χ x) → ∃ f : G → ℂ, f ≠ 0 ∧ Continuous f ∧ (∀ g ∈ Γ, ∀ w, β g w * f (g + w) = f w) ∧ (∀ u, p u = 0 → (∀ x, β x u * χ (x + u) = χ x) → ∀ w, β w u * f (w + u) = f w) ∧ (∀ w, ContDiff ℝ ∞ fun v : V => f (w + ι v)) ∧ ∀ w z, deriv (fun t : ℝ => β w (ι (t • z)) * f (w + ι (t • z))) 0 + Complex.I * deriv (fun t : ℝ => β w (ι (t • J z)) * f (w + ι (t • J z))) 0 = 0 := by
  intro G V _ _ _ _ _ _ p ι β om J Γ U₀ U χ hpc hιc hp hl hr hd hn hβc hβ halt hJ hsym hpos hΓ hinj
    _ hfin hχ0 hχ1 hχz hχι hU hUinv
  obtain ⟨M, hM⟩ := exists_exponent om J

  obtain ⟨a, ha⟩ : ∃ a : V, series p ι β om J Γ χ a (ι (-a)) ≠ 0 := by
    have hs := summable_coeff p om J Γ U₀ χ hpos hinj hfin hχ0 hχ1 (fun _ => 1) (by simp) 0 0 M 0
    simp only [one_mul, add_zero, zero_mul, Real.exp_zero, mul_one] at hs
    obtain ⟨a, ha⟩ := GlobalTheory.charSeries_exists_ne_zero V Γ
      (fun g a => Complex.exp (2 * Real.pi * Complex.I * (om (p g) a : ℝ)))
      (fun g => χ g * Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g) (J (p g)) : ℝ))) 0
      (fun g a b => by rw [← Complex.exp_add]; congr 1; simp only [map_add]; push_cast; ring)
      (fun g a => by
        have : (2 * Real.pi * Complex.I * (om (p g) a : ℝ) : ℂ)
          = ((2 * Real.pi * om (p g) a : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I])
      (fun a => by simp)
      (fun g hg => by
        have h1 : p g ≠ 0 := fun h => hg (Subtype.ext (hinj g g.2 h))
        have h2 := (hpos _ h1).ne'
        refine ⟨(2 * om (p g) (J (p g)))⁻¹ • J (p g), ?_⟩
        have h3 : om (p g) ((2 * om (p g) (J (p g)))⁻¹ • J (p g)) = 1 / 2 := by
          rw [map_smul, smul_eq_mul]; field_simp
        simp only [h3]
        rw [← Complex.exp_pi_mul_I]
        congr 1; push_cast; ring)
      hs (by simp [hχz])
    exact ⟨a, by rw [series_neg hp hl hr hd hβ halt hχι]; exact ha⟩
  have hexp := fun w : G => GlobalTheory.expSeries_contDiff_and_hasDerivAt V Γ
    (fun g => β g w * β (ι a) (g + w) * χ (g + w) *
        Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ)))
    (fun g => M (p g + (a + p w)))
    (summable_coeff p om J Γ U₀ χ hpos hinj hfin hχ0 hχ1 (fun g => β g w * β (ι a) (g + w))
      (fun g => by rw [norm_mul, hn, hn, one_mul]) w (a + p w) M)
  have hexpand := series_expand (Γ := Γ) hp hl hr hβ hsym hχι (fun y v => M y v) hM a
  have hne : ∀ x y, β x y ≠ 0 := fun x y h => by simpa [h] using hn x y
  have hgauss : ContDiff ℝ ∞ fun v : V => Complex.exp (-(Real.pi / 2 : ℂ) * (om v (J v) : ℝ)) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_bilin om J))).cexp
  have hsmooth : ∀ w, ContDiff ℝ ∞ fun v : V => series p ι β om J Γ χ a (w + ι v) := by
    intro w
    have h1 : ContDiff ℝ ∞ fun v : V => Complex.exp (Real.pi * Complex.I * (om (p w) v : ℝ)) :=
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (LinearMap.toContinuousLinearMap (om (p w))).contDiff)).cexp
    have h2 := h1.mul (hgauss.mul (hexp w).1)
    refine (congrArg (ContDiff ℝ ∞) (funext fun v => ?_)).mp h2
    rw [← hexpand w v, hβ, ← mul_assoc, ← Complex.exp_add]
    simp
  refine ⟨series p ι β om J Γ χ a, fun h => ha (by rw [h]; rfl), ?_,
    fun g hg w => series_quasi hl hr hΓ a g hg w,
    fun u hu hχ w => series_inv hl hr hd hβ a u hu hχ w, hsmooth, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro w
    have hc1 : Continuous fun x : G => p (x - w) := hpc.comp (continuous_id.sub continuous_const)
    have hc2 : Continuous fun x : G => β (w + ι (p (x - w))) ((x - w) - ι (p (x - w))) :=
      hβc.comp (f := fun x : G => (w + ι (p (x - w)), (x - w) - ι (p (x - w))))
        ((continuous_const.add (hιc.comp hc1)).prodMk
          ((continuous_id.sub continuous_const).sub (hιc.comp hc1)))
    have hc3 : Continuous fun x : G => (β (w + ι (p (x - w))) ((x - w) - ι (p (x - w))))⁻¹ *
        series p ι β om J Γ χ a (w + ι (p (x - w))) :=
      (hc2.inv₀ fun x => hne _ _).mul ((hsmooth w).continuous.comp hc1)
    refine hc3.continuousAt.congr ?_
    have hnhds : ∀ᶠ x in nhds w, x - w ∈ U := by
      have : IsOpen {x : G | x - w ∈ U} := hU.preimage (continuous_id.sub continuous_const)
      exact this.mem_nhds (by simp)
    filter_upwards [hnhds] with x hx
    have h := series_inv (Γ := Γ) (J := J) hl hr hd hβ a ((x - w) - ι (p (x - w)))
      (by rw [map_sub p, hp, sub_self]) (hUinv _ hx) (w + ι (p (x - w)))
    rw [← h, ← mul_assoc, inv_mul_cancel₀ (hne _ _), one_mul]
    congr 1; abel
  · intro w z
    have hder : ∀ z : V, HasDerivAt
        (fun t : ℝ => β w (ι (t • z)) * series p ι β om J Γ χ a (w + ι (t • z)))
        (∑' g : Γ, (β g w * β (ι a) (g + w) * χ (g + w) *
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))) *
          M (p g + (a + p w)) z) 0 := by
      intro z
      have g1 : HasDerivAt (fun t : ℝ =>
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (t • z) (J (t • z)) : ℝ))) 0 0 := by
        have g0 : HasDerivAt (fun t : ℝ => om (t • z) (J (t • z))) 0 0 := by
          have := ((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (om z (J z))
          refine (this.congr_deriv (by simp)).congr_of_eventuallyEq
            (Filter.Eventually.of_forall fun t => ?_)
          simp [mul_assoc]
        exact (g0.ofReal_comp.const_mul (-(Real.pi / 2 : ℂ))).cexp.congr_deriv (by simp)
      have g2 := g1.mul ((hexp w).2 z).2
      simp only [hexpand]
      exact g2.congr_deriv (by simp)
    rw [(hder z).deriv, (hder (J z)).deriv, ← tsum_mul_left,
      ← ((hexp w).2 z).1.tsum_add (((hexp w).2 (J z)).1.mul_left Complex.I)]
    refine (tsum_congr fun g => ?_).trans tsum_zero
    rw [hM, hM, hJ, map_neg]
    push_cast
    linear_combination (-(Real.pi : ℂ) * (β g w * β (ι a) (g + w) * χ (g + w) *
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))) *
          (om (p g + (a + p w)) (J z) : ℝ)) * Complex.I_mul_I
end GlobalTheory.HeisenbergGaussianSeries
