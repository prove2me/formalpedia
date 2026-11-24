-- Prove2me | solution 1 for GlobalTheory.RealWeil.proj_heis_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:08:40.280705+00:00
-- url     : https://prove2.me/submissions/4f91ee9d-641d-4342-b514-160e501dc705

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Theorems.Thm_GlobalTheory_RealWeil_integral_gau_twisted_conv
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_continuous
import Theorems.Thm_GlobalTheory_RealWeil_omJ_skew
import Theorems.Thm_GlobalTheory_RealWeil_proj_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
namespace GlobalTheory.RealWeil
theorem _root_.solution {ρ : V → B →L[ℂ] B} (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (a : V) (f : B) :
    proj h (ρ a (proj h f)) = gau a • proj h f := by
  have hself : ∀ x : V, omJ J x x = 0 := fun x => by
    have := omJ_skew hJ x x
    linarith
  set F : V → V → B := fun u z =>
    (gau u * (gau (z - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) z : ℝ) : ℂ)))) • ρ z f with hF
  have hin : ∀ u, gau u • ρ u (ρ a (proj h f)) = ∫ z, F u z := by
    intro u
    rw [h.2.1 u a, proj_apply h f, ← (ρ (u + a)).integral_comp_comm (h.integrable f), ← integral_smul,
      ← integral_smul, ← integral_add_right_eq_self (F u) (u + a)]
    congr 1
    ext w
    have hw : omJ J (u + a) (w + (u + a)) = omJ J (u + a) w := by
      have h0 := hself (u + a)
      unfold omJ at h0 ⊢
      rw [map_add, inner_add_right, h0, add_zero]
    show _ = (gau u * (gau (w + (u + a) - (u + a)) *
      cexp (π * I * ((omJ J u a + omJ J (u + a) (w + (u + a)) : ℝ) : ℂ)))) • ρ (w + (u + a)) f
    rw [add_sub_cancel_right, hw, add_comm w (u + a), map_smul, h.2.1 (u + a) w, smul_smul, smul_smul,
      smul_smul]
    congr 1
    push_cast
    rw [mul_add, Complex.exp_add]
    ring
  have he : ∀ r : ℝ, ‖cexp (π * I * (r : ℂ))‖ = 1 := fun r => by
    rw [Complex.norm_exp]
    simp
  have hnorm : ∀ u z, ‖F u z‖ = ‖gau u‖ * (‖gau (z - (u + a))‖ * ‖f‖) := by
    intro u z
    simp only [hF, norm_smul, norm_mul, h.2.2.1]
    rw [he, mul_one, mul_assoc]
  have hom : Continuous fun p : V × V => omJ J p.1 p.2 := by
    unfold omJ
    exact continuous_fst.inner (J.continuous.comp continuous_snd)
  have hcont : Continuous (Function.uncurry F) := by
    show Continuous fun p : V × V => (gau p.1 * (gau (p.2 - (p.1 + a)) *
      cexp (π * I * ((omJ J p.1 a + omJ J (p.1 + a) p.2 : ℝ) : ℂ)))) • ρ p.2 f
    refine Continuous.smul ?_ ((h.2.2.2 f).comp continuous_snd)
    refine (continuous_gau.comp continuous_fst).mul
      ((continuous_gau.comp (continuous_snd.sub (continuous_fst.add continuous_const))).mul ?_)
    refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    exact (hom.comp (continuous_fst.prodMk continuous_const)).add
      (hom.comp ((continuous_fst.add continuous_const).prodMk continuous_snd))
  have hint : Integrable (Function.uncurry F) ((volume : Measure V).prod volume) := by
    rw [integrable_prod_iff hcont.aestronglyMeasurable]
    constructor
    · refine Filter.Eventually.of_forall fun u => ?_
      have hm : AEStronglyMeasurable (fun z => Function.uncurry F (u, z)) volume :=
        (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      rw [← integrable_norm_iff hm]
      simp only [Function.uncurry_apply_pair, hnorm]
      exact (((integrable_gau (V := V)).norm.comp_sub_right (u + a)).mul_const ‖f‖).const_mul ‖gau u‖
    · simp only [Function.uncurry_apply_pair, hnorm]
      simp only [integral_const_mul, integral_mul_const, integral_sub_right_eq_self (‖gau ·‖)]
      exact (integrable_gau (V := V)).norm.mul_const _
  rw [proj_apply h (ρ a (proj h f))]
  simp_rw [hin]
  rw [integral_integral_swap hint]
  have hinner : ∀ z, ∫ u, F u z = (gau a * gau z) • ρ z f := by
    intro z
    simp only [hF]
    rw [integral_smul_const, integral_gau_twisted_conv hJ a z]
  simp_rw [hinner]
  rw [proj_apply h f, ← integral_smul]
  congr 1
  ext z
  rw [smul_smul]
end GlobalTheory.RealWeil
