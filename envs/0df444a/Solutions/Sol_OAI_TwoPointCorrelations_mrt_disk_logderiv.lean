-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_disk_logderiv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:31:27.467601+00:00
-- url     : https://prove2.me/submissions/8f656191-d5ef-4e32-a599-a1429616cd47

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_Erdos970_lem_analytic_zero_factor
import Theorems.Thm_Erdos970_lem_sum_m_rho_bound
import Theorems.Thm_Erdos970_log_of_analytic

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log













































attribute [fun_prop] measurable_from_top












section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end












































end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT1_ComplexAnalysis
namespace Erdos970




























lemma real_part_of_diff (M : ℝ) (w : ℂ) : (2 * M - w).re = 2 * M - w.re := by
  simp [Complex.sub_re]

lemma real_part_of_diffz (M : ℝ) (f_z : ℂ) : (2 * M - f_z).re = 2 * M - f_z.re := real_part_of_diff M f_z

lemma inequality_reversal (x M : ℝ) (hxM : x ≤ M) : 2 * M - x ≥ M := by linarith

lemma real_part_lower_bound (w : ℂ) (M : ℝ) (_hM : M > 0) (h : w.re ≤ M) : 2 * M - w.re ≥ M := by apply inequality_reversal w.re M h


lemma real_part_lower_bound3 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : (2 * M - w).re > 0 := by
  rw [real_part_of_diffz]
  apply lt_of_le_of_lt'
  apply real_part_lower_bound
  exact hM
  exact h
  exact hM

lemma nonzero_if_real_part_positive (w : ℂ) (hw_re_pos : w.re > 0) : w ≠ 0 := by
  by_contra h
  rw [h] at hw_re_pos
  exact lt_irrefl 0 hw_re_pos

lemma lem_real_part_lower_bound4 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : (2 * M - w) ≠ 0 := by
  apply nonzero_if_real_part_positive
  exact real_part_lower_bound3 w M hM h

lemma lem_abspos (z : ℂ) : z ≠ 0 → norm z > 0 := by
  intro h_ne_zero
  apply Real.sqrt_pos.mpr
  exact Complex.normSq_pos.mpr h_ne_zero

lemma lem_real_part_lower_bound5 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : norm (2 * M - w) > 0 := by
  apply lem_abspos
  exact lem_real_part_lower_bound4 w M hM h








lemma lem_modulus_sq_ReImw (M : ℝ) (w : ℂ) : norm (2 * M - w) ^ 2 - norm w ^ 2 = 4 * M * (M - w.re) := by
  simp_rw [Complex.sq_norm]
  simp_rw [Complex.normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma lem_modulus_sq_identity (M : ℝ) (w : ℂ) : norm (2 * M - w) ^ 2 - norm w ^ 2 = 4 * M * (M - w.re) := lem_modulus_sq_ReImw M w

lemma lem_nonnegative_product (M x : ℝ) (hM : M > 0) (hxM : x ≤ M) : 4 * M * (M - x) ≥ 0 := by
  have h_four_M_nonneg : 4 * M ≥ 0 := by linarith [hM]
  have h_diff_nonneg : M - x ≥ 0 := by linarith [hxM]
  apply mul_nonneg h_four_M_nonneg h_diff_nonneg

lemma lem_nonnegative_product2 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : 4 * M * (M - w.re) ≥ 0 := by
  apply lem_nonnegative_product
  exact hM
  exact hw_re_le_M

lemma lem_nonnegative_product3 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ^ 2 - norm w ^ 2 ≥ 0 := by
  rw [lem_modulus_sq_identity]
  apply lem_nonnegative_product2
  exact hM
  exact hw_re_le_M

lemma lem_nonnegative_product4 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ^ 2 ≥ norm w ^ 2 := by
  have h := lem_nonnegative_product3 M w hM hw_re_le_M
  linarith

lemma lem_nonnegative_product5 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ≥ norm w := by
  have h_sq_ge : ‖2 * M - w‖ ^ 2 ≥ ‖w‖ ^ 2 := by
    apply lem_nonnegative_product4 M w hM hw_re_le_M
  rw [ge_iff_le] at h_sq_ge                                                

  apply (sq_le_sq₀ (norm_nonneg w) (norm_nonneg (2 * M - w))).mp
  exact h_sq_ge

lemma lem_nonnegative_product6 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm w ≤ norm (2 * M - w) := by apply lem_nonnegative_product5 M w hM hw_re_le_M

lemma lem_ineqmultr (a b c : ℝ) (hc : c > 0) (_ha : 0 ≤ a) (hab : a ≤ b) : a / c ≤ b / c := by
  apply div_le_div_of_nonneg_right
  exact hab
  linarith [hc]

lemma lem_ineqmultrbb (a b : ℝ) (hb : b > 0) (ha : 0 ≤ a) (hab : a ≤ b) : a / b ≤ 1 := by
  have h := lem_ineqmultr a b b hb ha hab
  rw [div_self (ne_of_gt hb)] at h
  exact h

lemma lem_nonnegative_product7 (M : ℝ) (w : ℂ) (_hM : M > 0) (h_abs_diff_pos : norm (2 * M - w) > 0) (h_abs_le_abs_diff : norm w ≤ norm (2 * M - w)) : norm w / norm (2 * M - w) ≤ 1 := by
                                                                                   
  have h_abs_w_nonneg : 0 ≤ ‖w‖ := norm_nonneg w

  apply lem_ineqmultrbb
  exact h_abs_diff_pos
  exact h_abs_w_nonneg
  exact h_abs_le_abs_diff

lemma lem_nonnegative_product8 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) (h_abs_le_abs_diff : norm w ≤
norm (2 * M - w)) : norm w / norm (2 * M - w) ≤ 1 := by
  apply lem_nonnegative_product7 M w
  exact hM
  apply lem_real_part_lower_bound5 w M hM hw_re_le_M
  exact h_abs_le_abs_diff

lemma lem_nonnegative_product9 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm w / norm (2 * M - w) ≤ 1 := by
  apply lem_nonnegative_product8
  exact hM
  exact hw_re_le_M
  apply lem_nonnegative_product6
  exact hM
  exact hw_re_le_M

lemma lem_triangle_ineq (N G : ℂ) : norm (N + G) ≤ norm N + norm G := by
  exact norm_add_le N G

lemma lem_triangleineqminus (N F : ℂ) : norm (N - F) ≤ norm N + norm F := by
  rw [sub_eq_add_neg]
  calc
    ‖N + (-F)‖ ≤ ‖N‖ + ‖-F‖ := by apply lem_triangle_ineq
    _ = ‖N‖ + ‖F‖ := by rw [norm_neg]

lemma lem_rtriangle (r : ℝ) (N F : ℂ) (hr : r > 0) : r * norm (N - F) ≤ r * (norm N + norm F) := by
  apply mul_le_mul_of_nonneg_left
  apply lem_triangleineqminus
  linarith

lemma rtriangle2 (r : ℝ) (N F : ℂ) (hr : r > 0) : r * norm (N - F) ≤ r * norm N + r * norm F := by
  have h := lem_rtriangle r N F hr
  linarith [h]

lemma lem_rtriangle3 (r R : ℝ) (N F : ℂ) (hr : r > 0) (_hR : r < R) (h : R * norm F ≤ r * norm (N - F)) : R * norm F ≤ r * norm N + r * norm F := by
  calc
    R * norm F ≤ r * norm (N - F) := by exact h
    _ ≤ r * norm N + r * norm F := by apply rtriangle2 r N F hr

lemma lem_rtriangle4 (r R : ℝ) (N F : ℂ) (hr : 0 < r) (hR : r < R) (h_hyp : R * norm F ≤ r * norm (N - F)) : (R - r) * norm F ≤ r * norm N := by
  have h_result_from_lem3 : R * norm F ≤ r * norm N + r * norm F := by
    apply lem_rtriangle3 r R N F hr hR h_hyp
  linarith [h_result_from_lem3]




lemma lem_rtriangle5 (r R M : ℝ) (F : ℂ) (hr : 0 < r) (hrR : r < R) (hM : M > 0)
    (h_hyp : R * norm F ≤ r * norm (2 * M - F)) :
(R - r) * norm F ≤ 2 * M * r := by
                                        
  have h1 : (R - r) * norm F ≤ r * norm (2 * M : ℂ) :=
    lem_rtriangle4 r R (2 * M : ℂ) F hr hrR h_hyp

  have h2 : norm (2 * M : ℂ) = 2 * M := by

    have h_pos : (2 * M : ℝ) > 0 := by linarith [hM]
                                                                        
    convert (preTransparency := .instances) Complex.norm_of_nonneg (le_of_lt h_pos) using 1
                                                             
    norm_cast
                             
  rw [h2] at h1
                                     
  rw [mul_comm r (2 * M)] at h1
  exact h1

lemma lem_RrFpos (r R : ℝ) (F : ℂ) (_hr : 0 < r) (hrR : r < R) : (R - r) * norm F ≥ 0 := by
  have h_R_minus_r_nonneg : R - r ≥ 0 := by linarith [hrR]
  have h_abs_F_nonneg : 0 ≤ norm F := by apply norm_nonneg
  apply mul_nonneg h_R_minus_r_nonneg h_abs_F_nonneg

lemma lem_rtriangle6 (r R M : ℝ) (F : ℂ) (hr : 0 < r) (hrR : r < R) (_hM : M > 0)
    (h_hyp : (R - r) * norm F ≤ 2 * M * r) :
norm F ≤ (2 * M * r) / (R - r) := by
  have h_R_minus_r_pos : R - r > 0 := by linarith [hrR]
  have h_numerator_nonneg : 0 ≤ (R - r) * ‖F‖ := by apply lem_RrFpos r R F hr hrR
                                                                          
  have h_ineq_with_denominators : ( (R - r) * ‖F‖ ) / (R - r) ≤ (2 * M * r) / (R - r) := by
    apply lem_ineqmultr
    exact h_R_minus_r_pos          
    exact h_numerator_nonneg          
    exact h_hyp          
                                                                        
  rw [mul_div_cancel_left₀ (‖F‖) (ne_of_gt h_R_minus_r_pos)] at h_ineq_with_denominators
                                                     
  exact h_ineq_with_denominators

lemma lem_rtriangle7 (r R M : ℝ) (F : ℂ)
    (hr : 0 < r) (hrR : r < R) (hM : M > 0)
    (h_hyp : R * norm F ≤ r * norm (2 * M - F)) :
norm F ≤ (2 * M * r) / (R - r) := by
  have h_step1 := lem_rtriangle5 r R M F hr hrR hM h_hyp
  apply lem_rtriangle6 r R M F hr hrR hM h_step1



theorem analyticWithinAt_to_analyticAt_aux {f : ℂ → ℂ} {S : Set ℂ} {z : ℂ} (_hS : S ∈ nhds z)
  (p : FormalMultilinearSeries ℂ ℂ ℂ) (r : ENNReal) (_h_conv_on_inter : r ≤ p.radius) (_hr_pos : 0 < r)
  (hasSumt : ∀ {y : ℂ}, z + y ∈ insert z S → y ∈ Metric.eball 0 r → HasSum (fun n => (p n) fun _x => y) (f (z + y)))
  (ε : ℝ) (hε_pos : ε > 0) (h_ball_subset_S : Metric.ball z ε ⊆ S) :
  let r' := min r (ENNReal.ofReal ε);
  ∀ {y : ℂ}, y ∈ Metric.eball 0 r' → HasSum (fun n => (p n) fun _x => y) (f (z + y)) := by
  intro r' y hy
  apply hasSumt
  ·                            

    right                                              
    apply h_ball_subset_S
    rw [Metric.mem_ball]
                                      
    simp
                               
    have : y ∈ Metric.eball 0 (ENNReal.ofReal ε) := by
      apply Metric.eball_subset_eball (min_le_right r (ENNReal.ofReal ε)) hy

    have ε_nn : ENNReal.ofReal ε = ↑(ε.toNNReal) := by
      simp [ENNReal.ofReal]
    rw [ε_nn] at this
    rw [@Metric.eball_coe] at this
    simpa [Metric.mem_ball, dist_self_add_right, Real.toNNReal_of_nonneg hε_pos.le]

  ·                              
    exact Metric.eball_subset_eball (min_le_left r (ENNReal.ofReal ε)) hy

theorem analyticWithinAt_to_analyticAt {f : ℂ → ℂ} {S : Set ℂ} {z : ℂ}
    (hS : S ∈ nhds z) (h : AnalyticWithinAt ℂ f S z) : AnalyticAt ℂ f z := by
  rcases h with ⟨p, hp⟩

  use p

  rcases hp with ⟨r, h_conv_on_inter, hr_pos⟩

  rcases Metric.mem_nhds_iff.mp hS with ⟨ε, hε_pos, h_ball_subset_S⟩

  let r' := min r (ENNReal.ofReal ε)
  use r'

  constructor

  · exact inf_le_of_left_le h_conv_on_inter

  ·
    exact lt_min hr_pos (ENNReal.ofReal_pos.mpr hε_pos)
  rename_i hasSumt
  exact analyticWithinAt_to_analyticAt_aux hS p r h_conv_on_inter hr_pos hasSumt ε hε_pos h_ball_subset_S



lemma lem_1zanalDR (R : ℝ) (_hR_pos : 0 < R) :
    AnalyticOn ℂ (fun z ↦ z⁻¹) {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by

  apply AnalyticOn.mono (analyticOn_inv)
                                                     
  intro z hz
                                                       
  exact hz.2

lemma lem_analprod {T : Set ℂ} {f1 f2 : ℂ → ℂ} (hf1 : AnalyticOn ℂ f1 T) (hf2 : AnalyticOn ℂ f2 T) :
    AnalyticOn ℂ (f1 * f2) T := by
  exact hf1.mul hf2



lemma lem_fzzTanal {R : ℝ} (hR_pos : 0 < R) (f : ℂ → ℂ)
    (hf : AnalyticOn ℂ f (Metric.closedBall 0 R)) :
    AnalyticOn ℂ (fun z ↦ f z / z) {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by
                          
  rw [show (fun z ↦ f z / z) = (fun z ↦ f z) * (fun z ↦ z⁻¹) by ext; simp [div_eq_mul_inv]]
                                
  let T := {z : ℂ | norm z ≤ R ∧ z ≠ 0}
                                                            
  have hf_on_T : AnalyticOn ℂ f T := hf.mono (?_)
                         
  have h_inv_on_T : AnalyticOn ℂ (fun z ↦ z⁻¹) T := lem_1zanalDR R hR_pos
                                                                
  exact lem_analprod hf_on_T h_inv_on_T
  intro z hz
  have hT : T = {z | norm z ≤ R ∧ z ≠ 0} := rfl
  rw [hT] at hz
  simp only [Set.mem_ofPred_eq] at hz
  simp only [Metric.mem_closedBall]
  simp only [dist_zero_right]
  exact hz.1

lemma lem_AnalOntoWithin {V : Set ℂ} {h : ℂ → ℂ} (hh : AnalyticOn ℂ h V) (z : ℂ) (hz : z ∈ V) :
    AnalyticWithinAt ℂ h V z := by
  exact hh z hz


lemma lem_DR0T {R : ℝ} (hR : 0 < R) :
    Metric.closedBall 0 R = {0} ∪ {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by
  ext z
  simp [Metric.closedBall, dist_zero_right]
  by_cases hz : z = 0
  · simp [hz, hR.le]
  · simp [hz]

lemma lem_analWWWithin {R : ℝ} (hR_pos : 0 < R) (h : ℂ → ℂ) :
    (AnalyticWithinAt ℂ h (Metric.closedBall 0 R) 0) →
    (∀ z ∈ {z : ℂ | norm z ≤ R ∧ z ≠ 0}, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) →
    (∀ z ∈ Metric.closedBall 0 R, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) := by
  intro h0 hT z hz
  rw [lem_DR0T hR_pos] at hz
  cases' hz with hz hz
  · simp at hz
    rw [hz]
    exact h0
  · exact hT z hz

lemma lem_analWWithinAtOn (R : ℝ) (hR_pos : 0 < R) (h : ℂ → ℂ)
    (h_at_0 : AnalyticWithinAt ℂ h (Metric.closedBall 0 R) 0)
    (h_at_T : ∀ z ∈ {z : ℂ | norm z ≤ R ∧ z ≠ 0}, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) :
    AnalyticOn ℂ h (Metric.closedBall 0 R) := by
  exact lem_analWWWithin hR_pos h h_at_0 h_at_T

lemma lem_AnalAttoWithin {h : ℂ → ℂ} {s : Set ℂ} (hh : AnalyticAt ℂ h 0) :
    AnalyticWithinAt ℂ h s 0 := by
  exact hh.analyticWithinAt

lemma analyticWithinAt_punctured_to_closedBall {R : ℝ} (_hR : 0 < R) {h : ℂ → ℂ} {z : ℂ} (hz : z ∈ {w : ℂ | norm w ≤ R ∧ w ≠ 0}) (h_within : AnalyticWithinAt ℂ h {w : ℂ | norm w ≤ R ∧ w ≠ 0} z) : AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z := by
                                                                                                                   
  apply AnalyticWithinAt.mono_of_mem_nhdsWithin h_within

  have hz_ne_zero : z ≠ 0 := hz.2

  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]

  use Metric.ball z (‖z‖ / 2)

  constructor
  ·                                      
    exact Metric.ball_mem_nhds z (half_pos (norm_pos_iff.mpr hz_ne_zero))

  ·                                                                                       
    intro w hw
    constructor
    ·                   
      have w_in_closedball : w ∈ Metric.closedBall 0 R := hw.2
      simp only [Metric.mem_closedBall, dist_zero_right] at w_in_closedball
                                           
      simp [w_in_closedball]
    ·              
      intro hw_eq_zero
      have w_in_ball : w ∈ Metric.ball z (‖z‖ / 2) := hw.1
      rw [hw_eq_zero] at w_in_ball
      simp only [Metric.mem_ball] at w_in_ball

      rw [dist_comm] at w_in_ball
      simp at w_in_ball
      have pos_norm : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne_zero
      linarith [pos_norm]

lemma lem_analAtOnOn {R : ℝ} (hR_pos : 0 < R) (h : ℂ → ℂ) :
    AnalyticAt ℂ h 0 →
    AnalyticOn ℂ h {z : ℂ | norm z ≤ R ∧ z ≠ 0} →
    AnalyticOn ℂ h (Metric.closedBall 0 R) := by
  intro h_at_0 h_on_punctured

  apply lem_analWWithinAtOn R hR_pos h

  · exact lem_AnalAttoWithin h_at_0

  · intro z hz
                                                       
    have h_within_punctured : AnalyticWithinAt ℂ h {w : ℂ | norm w ≤ R ∧ w ≠ 0} z :=
      lem_AnalOntoWithin h_on_punctured z hz
                                     
    exact analyticWithinAt_punctured_to_closedBall hR_pos hz h_within_punctured

lemma lem_orderne0 (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) :
    analyticOrderAt f 0 ≠ 0 := by exact (AnalyticAt.analyticOrderAt_ne_zero hf).mpr hf0

lemma lem_ordernetop (f : ℂ → ℂ) (_hf : AnalyticAt ℂ f 0) (hf_ne_zero : ¬(∀ᶠ z in nhds 0, f z = 0)) :
    analyticOrderAt f 0 ≠ ⊤ := by
  intro h
  rw [analyticOrderAt_eq_top] at h
  exact hf_ne_zero h

lemma lem_ordernatcast (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) (hn : analyticOrderAt f 0 = n) :
    ∃ (g : ℂ → ℂ), AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧ ∀ᶠ (z : ℂ) in nhds 0, f z = z ^ n * g z := by

  rw [AnalyticAt.analyticOrderAt_eq_natCast] at hn
  · convert (preTransparency := .instances) hn
    aesop
  · exact hf

lemma lem_ordernatcast1 (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) (hn : analyticOrderAt f 0 = n) (hn_ne_zero : n ≠ 0) :
    ∃ (h : ℂ → ℂ), AnalyticAt ℂ h 0 ∧ ∀ᶠ z in nhds 0, f z = z * h z := by
                           
  rcases lem_ordernatcast f hf n hn with ⟨g, hg_analytic, _, hf_eq_g⟩
                              
  use fun z ↦ z ^ (n - 1) * g z
  constructor
  ·                                                    
    exact (analyticAt_id.pow (n - 1)).mul hg_analytic
  ·                        
    filter_upwards [hf_eq_g] with z h_eq
    rw [h_eq]
    ring_nf
    rw [← pow_succ' z (n - 1), Nat.sub_add_cancel (Nat.pos_of_ne_zero hn_ne_zero)]

lemma lem_ordernatcast2_old (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (h_not_eventually_zero : ¬ (∀ᶠ z in nhds 0, f z = 0)) :
    ∃ (h : ℂ → ℂ), AnalyticAt ℂ h 0 ∧ ∀ᶠ z in nhds 0, f z = z * h z := by
                                 
  let n₀ := analyticOrderAt f 0
                                                                        
  have hn_ne_top : n₀ ≠ ⊤ := lem_ordernetop f hf h_not_eventually_zero
                                             
  lift n₀ to ℕ using hn_ne_top with n hn_eq
                                                  
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    rw [hn_zero] at hn_eq

    have t := (lem_orderne0 f hf hf0)
    have : n₀ = analyticOrderAt f 0 := rfl
    rw [←this] at t
    exact t (id (Eq.symm hn_eq))
                                                                       
  exact lem_ordernatcast1 f hf n (by aesop) hn_ne_zero

lemma lem_ordernatcast2 {R : ℝ} (hR_pos : 0 < R) (f : ℂ → ℂ) (hf0 : f 0 = 0)
    (hf : AnalyticOn ℂ f (Metric.closedBall 0 R)) :
    AnalyticAt ℂ (fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z) 0 := by
                                                                            
  have hS : Metric.closedBall 0 R ∈ nhds (0 : ℂ) := by
                                                              
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) hR_pos) ?subset
    exact Metric.ball_subset_closedBall
  have hf_within : AnalyticWithinAt ℂ f (Metric.closedBall 0 R) 0 := hf 0 (by
    simp [Metric.mem_closedBall, hR_pos.le])
  have hf_at0 : AnalyticAt ℂ f 0 := analyticWithinAt_to_analyticAt hS hf_within

  let g : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z

  by_cases hEZ : (∀ᶠ z in nhds (0 : ℂ), f z = 0)
  ·                                                                                          
                                          
    have hU : {z : ℂ | f z = 0} ∈ nhds (0 : ℂ) := by simpa only [Filter.Eventually] using hEZ
                                        
    have hf_eq_zero : f =ᶠ[nhds (0 : ℂ)] (fun _ : ℂ => 0) := by
      refine (Filter.eventuallyEq_iff_exists_mem).2 ?_
      exact ⟨{z | f z = 0}, hU, by intro z hz; simpa [Set.mem_ofPred_eq] using hz⟩
                                                                    
    have h_fderiv_zero : (fderiv ℂ f 0) = 0 := by
      simpa using (Filter.EventuallyEq.fderiv_eq hf_eq_zero)

    have h_g_zero_on_U : ∀ z ∈ {z : ℂ | f z = 0}, g z = 0 := by
      intro z hzU
      by_cases hz0 : z = 0
      ·                                  
        simp [g, hz0, h_fderiv_zero]
      ·                                  
        have : f z = 0 := by simpa [Set.mem_ofPred_eq] using hzU
        simp [g, hz0, this]
                                                                                  
    have h_const0_within : AnalyticWithinAt ℂ (fun _ : ℂ => (0 : ℂ)) {z : ℂ | f z = 0} 0 :=
      analyticAt_const.analyticWithinAt
    have h_g_within : AnalyticWithinAt ℂ g {z : ℂ | f z = 0} 0 := by
                                        
      apply h_const0_within.congr
      intro z hz
      by_cases hz0 : z = 0
      ·        
        simp [g, hz0, h_fderiv_zero]
      ·             
        have : f z = 0 := by simpa [Set.mem_ofPred_eq] using hz
        simp [g, hz0, this]
                           
      simp [g, h_fderiv_zero]
    exact analyticWithinAt_to_analyticAt hU h_g_within

  ·                                                                
    have h_notEZ : ¬ (∀ᶠ z in nhds (0 : ℂ), f z = 0) := hEZ
                                                        
    rcases lem_ordernatcast2_old f hf_at0 hf0 h_notEZ with ⟨h0, h0_at0, hfac_ev⟩
                                                               
    have hV : {z : ℂ | f z = z * h0 z} ∈ nhds (0 : ℂ) := by simpa only [Filter.Eventually] using hfac_ev
    have h_eq_nhds : f =ᶠ[nhds (0 : ℂ)] (fun z => z * h0 z) :=
      (Filter.eventuallyEq_iff_exists_mem).2 ⟨{z : ℂ | f z = z * h0 z}, hV, by
        intro z hz; simpa [Set.mem_ofPred_eq] using hz⟩
                              
    have h_fderiv_prod : fderiv ℂ f 0 = fderiv ℂ (fun z => z * h0 z) 0 :=
      Filter.EventuallyEq.fderiv_eq h_eq_nhds
                                                                              
    have h_diff_id : DifferentiableAt ℂ (fun z : ℂ => z) 0 := differentiableAt_id
    have h_diff_h0 : DifferentiableAt ℂ h0 0 := h0_at0.differentiableAt
                             
    have h_val0 : (fderiv ℂ f 0) 1 = h0 0 := by
                                                           
      rw [h_fderiv_prod]
      rw [fderiv_fun_mul' h_diff_id h_diff_h0]
      simp only [add_apply, smul_apply]
      rw [fderiv_fun_id]
      simp only [ContinuousLinearMap.id_apply]
      simp only [zero_smul, zero_add]
      simp

    have h_geq_h0_on_V : ∀ z ∈ {z : ℂ | f z = z * h0 z}, g z = h0 z := by
      intro z hzU
      by_cases hz0 : z = 0
      ·        
        simpa [g, hz0] using h_val0
      ·                                    
        have : f z = z * h0 z := by simpa [Set.mem_ofPred_eq] using hzU
        simp only [g, if_neg hz0, this]
        exact mul_div_cancel_left₀ (h0 z) hz0
                                                                    
    have h0_within : AnalyticWithinAt ℂ h0 {z : ℂ | f z = z * h0 z} 0 := h0_at0.analyticWithinAt
    have hg_within : AnalyticWithinAt ℂ g {z : ℂ | f z = z * h0 z} 0 := by

      apply AnalyticWithinAt.congr h0_within
                                 
      intro z hz
      exact h_geq_h0_on_V z hz

      have h_0_in_V : (0 : ℂ) ∈ {z : ℂ | f z = z * h0 z} := by
        simp [hf0]
      exact h_geq_h0_on_V 0 h_0_in_V
    exact analyticWithinAt_to_analyticAt hV hg_within



lemma lem_inDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw : w ∈ closure (ballDR R)) : norm w ≤ R := by
  rw [lem_ballDR R hR] at hw
  rw [Metric.mem_closedBall] at hw
  rw [Complex.dist_eq] at hw
  simp at hw
  exact hw

lemma lem_notinDR (R : ℝ) (_hR : R > 0) (w : ℂ) (hw : w ∉ ballDR R) : norm w ≥ R := by
                               
  unfold ballDR at hw
                                                   
  rw [Metric.mem_ball] at hw
                                                              
  push Not at hw
                                                                     
  rw [Complex.dist_eq] at hw
                       
  simp at hw
  exact hw

lemma lem_legeR (R : ℝ) (_hR : R > 0) (w : ℂ) (hw1 : norm w ≤ R) (hw2 : norm w ≥ R) : norm w = R := by
  linarith

lemma lem_circleDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw1 : w ∈ closure (ballDR R)) (hw2 : w ∉ ballDR R) : norm w = R := by
  have h1 : norm w ≤ R := lem_inDR R hR w hw1
  have h2 : norm w ≥ R := lem_notinDR R hR w hw2
  exact lem_legeR R hR w h1 h2

lemma lem_Rself (R : ℝ) (hR : R > 0) : |R| = R := by
  rw [abs_eq_self]
  linarith

lemma lem_Rself2 (R : ℝ) (hR : R > 0) : |R| ≤ R := by
  rw [lem_Rself R hR]

lemma lem_Rself3 (R : ℝ) (hR : R > 0) : (R : ℂ) ∈ closure (ballDR R) := by
  rw [lem_ballDR R hR]
  rw [Metric.mem_closedBall]
  simp
  exact lem_Rself2 R hR


lemma lem_ExtrValThm {K : Set ℂ} (hK : IsCompact K) (hK_nonempty : K.Nonempty) (g : K → ℂ) (hg : Continuous g) :
∃ v : K, ∀ z : K, norm (g z) ≤ norm (g v) := by
                                       
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
                            
  have : Nonempty K := hK_nonempty.to_subtype
                                                             
  let f : K → ℝ := fun z => norm (g z)
                                
  have hf_cont : Continuous f := continuous_norm.comp hg
                                                       
  obtain ⟨v, hv_mem, hv_max⟩ := IsCompact.exists_isMaxOn isCompact_univ Set.univ_nonempty hf_cont.continuousOn
  use v
  intro z
  exact hv_max (Set.mem_univ z)

lemma lem_ExtrValThmDR (R : ℝ) (hR : R > 0) (g : closure (ballDR R) → ℂ) (hg : Continuous g) :
∃ v : closure (ballDR R), ∀ z : closure (ballDR R), norm (g z) ≤ norm (g v) := by
                                                     
  have hK_compact : IsCompact (closure (ballDR R)) := lem_DRcompact R hR
                                             
  have hK_nonempty : (closure (ballDR R)).Nonempty := by
    rw [lem_ballDR R hR]
    rw [Metric.nonempty_closedBall]
    linarith
                                    
  exact lem_ExtrValThm hK_compact hK_nonempty g hg

lemma lem_AnalCont {R : ℝ} (_hR : R > 0) (H : ℂ → ℂ) (h_analytic : AnalyticOn ℂ H (closure (ballDR R))) :
Continuous (H ∘ (Subtype.val : closure (ballDR R) → ℂ)) := by
                                                                    
  have h_cont_on : ContinuousOn H (closure (ballDR R)) := AnalyticOn.continuousOn h_analytic
                              
  have h_val_cont : Continuous (Subtype.val : closure (ballDR R) → ℂ) := continuous_subtype_val

  exact ContinuousOn.comp_continuous h_cont_on h_val_cont (fun _ => Subtype.mem _)

lemma lem_ExtrValThmh {R : ℝ} (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ u : closure (ballDR R), ∀ z : closure (ballDR R), norm (h u) ≥ norm (h z) := by
                                                    
  have hg_continuous : Continuous (h ∘ Subtype.val : closure (ballDR R) → ℂ) :=
    lem_AnalCont hR h h_analytic
                                              
  obtain ⟨v, hv⟩ := lem_ExtrValThmDR R hR (h ∘ Subtype.val) hg_continuous
                   
  use v
                                        
  intro z
  have : norm ((h ∘ Subtype.val) z) ≤ norm ((h ∘ Subtype.val) v) := hv z
                             
  simp [Function.comp] at this
  exact this

lemma lem_MaxModP (R : ℝ) (_hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) : ∀ z ∈ closure (ballDR R), norm (h z) = norm (h w) := by
                                                             
  have h_preconnected : IsPreconnected (ballDR R) := by
    unfold ballDR
    apply Convex.isPreconnected
    exact convex_ball (0 : ℂ) R

  have h_open : IsOpen (ballDR R) := by
    unfold ballDR
    exact Metric.isOpen_ball

  have h_diff_cont : DiffContOnCl ℂ h (ballDR R) := by
    constructor
    ·                                   
      apply AnalyticOn.differentiableOn
      exact h_analytic.mono subset_closure
    ·                                         
      exact AnalyticOn.continuousOn h_analytic

  have h_max_on : IsMaxOn (norm ∘ h) (ballDR R) w := by
    intro z hz
    change ‖h z‖ ≤ ‖h w‖
    exact hw_max z hz

  have h_eq := Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn h_preconnected h_open h_diff_cont hw_in_DR h_max_on

  intro z hz
  have norm_eq := h_eq hz
  simp only [Function.comp_apply, Function.const_apply] at norm_eq
                                                                                   
  convert (preTransparency := .instances) norm_eq

lemma lem_MaxModR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) : norm (h R) = norm (h w) := by
                                                                
  have h_const : ∀ z ∈ closure (ballDR R), norm (h z) = norm (h w) :=
    lem_MaxModP R hR h h_analytic w hw_in_DR hw_max
                                                      
  have hR_in_closure : (R : ℂ) ∈ closure (ballDR R) := lem_Rself3 R hR
                                         
  exact h_const (R : ℂ) hR_in_closure

lemma lem_MaxModRR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) :
∀ z ∈ closure (ballDR R), norm (h R) ≥ norm (h z) := by
  intro z hz
                                                                            
  have h1 := lem_MaxModP R hR h h_analytic w hw_in_DR hw_max z hz
                                             
  have h2 := lem_MaxModR R hR h h_analytic w hw_in_DR hw_max
                                                                             
  rw [h2, h1]

theorem lem_MaxModv2 (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ v : closure (ballDR R), norm (v : ℂ) = R ∧ ∀ z : closure (ballDR R), norm (h (v : ℂ)) ≥ norm (h (z : ℂ)) := by
                                                       
  obtain ⟨u, hu⟩ := lem_ExtrValThmh hR h h_analytic

  if h_case : (u : ℂ) ∈ ballDR R then
                                 
    have hR_in_closure : (R : ℂ) ∈ closure (ballDR R) := lem_Rself3 R hR
    let v : closure (ballDR R) := ⟨R, hR_in_closure⟩
    use v
    constructor
    ·                
                                                                             
      have v_eq : (v : ℂ) = (R : ℂ) := rfl
      rw [v_eq]
                                                                               
      have : norm (R : ℂ) = abs R := by
        simp [Complex.norm_real]
      rw [this, lem_Rself R hR]
    ·                                                     
      intro z
                                                                        
      have hw_max : ∀ w ∈ ballDR R, norm (h w) ≤ norm (h (u : ℂ)) := by
        intro w hw
                                                      
        have hw_closure : w ∈ closure (ballDR R) := subset_closure hw
                                              
        let w_sub : closure (ballDR R) := ⟨w, hw_closure⟩
        exact hu w_sub
                                             
      have h_result := lem_MaxModRR R hR h h_analytic (u : ℂ) h_case hw_max
                                                  
      have v_eq : (v : ℂ) = (R : ℂ) := rfl
      rw [v_eq]
                                                           
      exact h_result (z : ℂ) (Subtype.mem z)
  else
                                 
    use u
    constructor
    ·                                   
      exact lem_circleDR R hR (u : ℂ) (Subtype.mem u) h_case
    ·                                                                  
      exact hu

theorem lem_MaxModv3 (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ v : ℂ, norm v = R ∧ ∀ z : ℂ, z ∈ closure (ballDR R) → norm (h v) ≥ norm (h z) := by
                                                                                   
  obtain ⟨v_sub, hv_abs, hv_max⟩ := lem_MaxModv2 R hR h h_analytic
                                                           
  let v := (v_sub : ℂ)
  use v
  constructor
  ·                
    exact hv_abs
  ·                            
    intro z hz
                                               
    have hz_sub : z ∈ closure (ballDR R) := hz
    let z_sub : closure (ballDR R) := ⟨z, hz_sub⟩
    have := hv_max z_sub
                             
    simp at this
    exact this

lemma lem_MaxModv4 (R B : ℝ) (hR : R > 0) (_hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∃ v : ℂ, norm v = R ∧ (∀ w : ℂ, w ∈ closure (ballDR R) → norm (h v) ≥ norm (h w)) ∧ norm (h v) ≤ B := by
                                                                             
  obtain ⟨v, hv_abs, hv_max⟩ := lem_MaxModv3 R hR h h_analytic
                         
  use v
  constructor
  ·           
    exact hv_abs
  constructor
  ·                                                  
    exact hv_max
  ·                                                  
    apply h_boundary_bound
    exact hv_abs

lemma lem_HardMMP (R B : ℝ) (hR : R > 0) (hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∀ w : ℂ, w ∈ closure (ballDR R) → norm (h w) ≤ B := by
  intro w hw
                                                                                            
  obtain ⟨v, hv_abs, hv_max, hv_bound⟩ := lem_MaxModv4 R B hR hB h h_analytic h_boundary_bound
                                
  have h1 : norm (h w) ≤ norm (h v) := hv_max w hw
  have h2 : norm (h v) ≤ B := hv_bound
                             
  linarith [h1, h2]

lemma lem_EasyMMP (R B : ℝ) (hR : R > 0) (_hB : B ≥ 0)
  (h : ℂ → ℂ) (_h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_closure_bound : ∀ w : ℂ, w ∈ closure (ballDR R) → norm (h w) ≤ B) :
∀ z : ℂ, norm z = R → norm (h z) ≤ B := by
  intro z hz
                                                  
  apply h_closure_bound z
                                     
  rw [lem_ballDR R hR]
  rw [Metric.mem_closedBall]
  rw [Complex.dist_eq]
  simp

  have : ‖z‖ = R := hz
  linarith

theorem lem_MMP (R B : ℝ) (hR : R > 0) (hB : B ≥ 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
(∀ z : ℂ, z ∈ closure (ballDR R) → norm (h z) ≤ B) ↔ (∀ z : ℂ, norm z = R → norm (h z) ≤ B) := by
  constructor
  ·                                                     
    intro h_closure_bound
    exact lem_EasyMMP R B hR hB h h_analytic h_closure_bound
  ·                                                      
    intro h_boundary_bound
    exact lem_HardMMP R B hR hB h h_analytic h_boundary_bound

lemma lem_denominator_nonzero (R M : ℝ) (_hR : R > 0) (hM : M > 0)
  (f : ℂ → ℂ) (_h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
  (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
∀ z : ℂ, z ∈ closure (ballDR R) → (2 * M - f z) ≠ 0 := by
  intro z hz
                                                  
  apply lem_real_part_lower_bound4 (f z) M hM
                                   
  exact h_re_bound z hz

lemma lem_f_vs_2M_minus_f (R M : ℝ) (_hR : R > 0) (hM : M > 0)
  (f : ℂ → ℂ) (_h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
  (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
∀ z : ℂ, z ∈ closure (ballDR R) → norm (f z) / norm (2 * M - f z) ≤ 1 := by
  intro z hz
                                                 
  apply lem_nonnegative_product9 M (f z) hM
                                   
  exact h_re_bound z hz


lemma lem_removable_singularity (R : ℝ) (hR : R > 0) (f : ℂ → ℂ)
  (h_analytic : AnalyticOn ℂ f (closure (ballDR R))) (h_zero : f 0 = 0) :
AnalyticOn ℂ (fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z) (closure (ballDR R)) := by
                                                                             
  rw [lem_ballDR R hR] at h_analytic ⊢

  let g : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z

  apply lem_analAtOnOn hR g

  ·                                
                                                   
    exact lem_ordernatcast2 hR f h_zero h_analytic

  ·                                                         

    have f_on_closedball : AnalyticOn ℂ f (Metric.closedBall 0 R) := h_analytic
    have quotient_analytic : AnalyticOn ℂ (fun z ↦ f z / z) {z : ℂ | ‖z‖ ≤ R ∧ z ≠ 0} :=
      lem_fzzTanal hR f f_on_closedball

    apply AnalyticOn.congr quotient_analytic
    intro z hz
                                                                 
    simp [g, if_neg hz.2]

lemma lem_quotient_analytic {R : ℝ} (_hR : R > 0) (h1 h2 : ℂ → ℂ)
  (h_analytic1 : AnalyticOn ℂ h1 (closure (ballDR R)))
  (h_analytic2 : AnalyticOn ℂ h2 (closure (ballDR R)))
  (h_nonzero : ∀ z ∈ closure (ballDR R), h2 z ≠ 0) :
AnalyticOn ℂ (fun z ↦ h1 z / h2 z) (closure (ballDR R)) := by
  exact AnalyticOn.div h_analytic1 h_analytic2 h_nonzero


lemma lem_g_analytic (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
AnalyticOn ℂ (f_M R M hR hM f h_analytic h_zero h_re_bound) (closure (ballDR R)) := by
                                                          
  let h₁ : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z
                              
  let h₂ : ℂ → ℂ := fun z ↦ 2 * M - f z

  have h_eq : f_M R M hR hM f h_analytic h_zero h_re_bound = fun z ↦ h₁ z / h₂ z := by
    ext z
    unfold f_M h₁ h₂
    simp

  rw [h_eq]

  apply lem_quotient_analytic hR

  · exact lem_removable_singularity R hR f h_analytic h_zero

  · have h₂_analytic : AnalyticOn ℂ h₂ (closure (ballDR R)) := by
      unfold h₂
      apply AnalyticOn.sub
      · exact analyticOn_const
      · exact h_analytic
    exact h₂_analytic

  · intro z hz
    unfold h₂
    exact lem_denominator_nonzero R M hR hM f h_analytic h_re_bound z hz

lemma lem_absab (a b : ℂ) (_hb : b ≠ 0) : norm (a / b) = norm a / norm b := by
  exact IsAbsoluteValue.abv_div norm a b

lemma lem_g_on_boundaryz (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_in_closure : z ∈ closure (ballDR R)) (hz_nonzero : z ≠ 0) :
  norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
norm (f z / z) / norm (2 * M - f z) := by
                              
  unfold f_M
                                                                
  simp only [if_neg hz_nonzero]

  have h_nonzero : (2 * M - f z) ≠ 0 := lem_denominator_nonzero R M hR hM f h_analytic h_re_bound z hz_in_closure
                    
  exact lem_absab (f z / z) (2 * M - f z) h_nonzero

lemma lem_fzzR (R : ℝ) (hR : R > 0) (z w : ℂ) (hz : norm z = R) : norm (w / z) = norm w / R := by
                          
  have hz_nonzero : z ≠ 0 := by
    intro h_eq
    rw [h_eq] at hz
    simp at hz
    linarith [hz, hR]
                    
  rw [lem_absab w z hz_nonzero]
                               
  rw [hz]

lemma lem_g_on_boundary (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_on_boundary : norm z = R) :
  norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
(norm (f z) / R) / norm (2 * M - f z) := by
                                            
  have hz_nonzero : z ≠ 0 := by
    intro h_eq
    rw [h_eq] at hz_on_boundary
    simp at hz_on_boundary
    linarith [hz_on_boundary, hR]

  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    convert (preTransparency := .instances) le_of_eq hz_on_boundary

  have h1 : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
    norm (f z / z) / norm (2 * M - f z) :=
    lem_g_on_boundaryz R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure hz_nonzero

  have h2 : norm (f z / z) = norm (f z) / R :=
    lem_fzzR R hR z (f z) hz_on_boundary

  rw [h1, h2]

lemma lem_f_vs_2M_minus_fR (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (_h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_in_closure : z ∈ closure (ballDR R)) :
(norm (f z) / R) / norm (2 * M - f z) ≤ 1 / R := by
                                               
  have h1 : norm (f z) / norm (2 * M - f z) ≤ 1 :=
    lem_f_vs_2M_minus_f R M hR hM f h_analytic h_re_bound z hz_in_closure

  rw [div_div]

  rw [mul_comm R]

  rw [← div_div]

  exact div_le_div_of_nonneg_right h1 (le_of_lt hR)

lemma lem_g_boundary_bound0 (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_on_boundary : norm z = R) :
norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) ≤ 1 / R := by
                                                          
  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    convert (preTransparency := .instances) le_of_eq hz_on_boundary

  rw [lem_g_on_boundary R M hR hM f h_analytic h_zero h_re_bound z hz_on_boundary]

  exact lem_f_vs_2M_minus_fR R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure

lemma lem_g_interior_bound (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
∀ z : ℂ, z ∈ closure (ballDR R) → norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) ≤ 1 / R := by
                      
  have hB : (1 / R : ℝ) ≥ 0 := div_nonneg zero_le_one (le_of_lt hR)
                                          
  have h_g_analytic : AnalyticOn ℂ (f_M R M hR hM f h_analytic h_zero h_re_bound) (closure (ballDR R)) :=
    lem_g_analytic R M hR hM f h_analytic h_zero h_re_bound
                                                                       
  apply (lem_MMP R (1 / R) hR hB (f_M R M hR hM f h_analytic h_zero h_re_bound) h_g_analytic).mpr
                                                                
  intro z hz_boundary
  exact lem_g_boundary_bound0 R M hR hM f h_analytic h_zero h_re_bound z hz_boundary

lemma lem_g_at_r (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
  norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
(norm (f z) / r) / norm (2 * M - f z) := by
                                            
  have hz_nonzero : z ≠ 0 := by
    intro h_eq
    rw [h_eq] at hz_on_boundary
    simp at hz_on_boundary
    linarith [hz_on_boundary, hr_pos]

  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    linarith [hz_on_boundary, hr_lt_R]

  have h1 : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
    norm (f z / z) / norm (2 * M - f z) :=
    lem_g_on_boundaryz R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure hz_nonzero

  have h2 : norm (f z / z) = norm (f z) / r :=
    lem_fzzR r hr_pos z (f z) hz_on_boundary

  rw [h1, h2]

lemma lem_g_at_rR (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
(norm (f z) / r) / norm (2 * M - f z) ≤ 1 / R := by
                                                       
  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    linarith [hz_on_boundary, hr_lt_R]

  have h_bound : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) ≤ 1 / R :=
    lem_g_interior_bound R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure

  have h_eq : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
    (norm (f z) / r) / norm (2 * M - f z) :=
    lem_g_at_r R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

  rw [← h_eq]
  exact h_bound

lemma lem_fracs (a b r R : ℝ) (ha : a > 0) (hb : b > 0) (hr : r > 0) (hR : R > 0)
(h_le : (a / r) / b ≤ 1 / R) : R * a ≤ r * b := by
                                              
  have h1 : (a / r) / b = a / (r * b) := by
    field_simp
  rw [h1] at h_le

  have h_pos_rb : 0 < r * b := mul_pos hr hb
  rw [div_le_div_iff₀ h_pos_rb hR] at h_le
                                      
  simp only [one_mul] at h_le

  linarith

lemma lem_nonneg_product_with_real_abs (r M : ℝ) (hr : r > 0) (hM : M > 0) : 0 ≤ r * (2 * |M|) := by
                                 
  have h_abs_eq : |M| = M := abs_of_pos hM
                                         
  rw [h_abs_eq]

  have h_two_M_pos : (2 : ℝ) * M > 0 := by
    apply mul_pos
    norm_num
    exact hM
                              
  apply mul_nonneg
  linarith [hr]
  linarith [h_two_M_pos]

lemma lem_f_bound_rearranged (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
R * norm (f z) ≤ r * norm (2 * M - f z) := by
                                     
  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    linarith [hz_on_boundary, hr_lt_R]

  have h_ineq : (norm (f z) / r) / norm (2 * M - f z) ≤ 1 / R :=
    lem_g_at_rR R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

  have h_denom_nonzero : (2 * M - f z) ≠ 0 :=
    lem_denominator_nonzero R M hR hM f h_analytic h_re_bound z hz_in_closure

  have h_denom_pos : norm (2 * M - f z) > 0 :=
    lem_abspos (2 * M - f z) h_denom_nonzero

  by_cases h_case : f z = 0
  ·                                                      
    rw [h_case]
    simp [mul_zero]
    exact lem_nonneg_product_with_real_abs r M hr_pos hM
  ·                                    
    have h_num_pos : norm (f z) > 0 :=
      lem_abspos (f z) h_case

    exact lem_fracs (norm (f z)) (norm (2 * M - f z)) r R
           h_num_pos h_denom_pos hr_pos hR h_ineq

lemma lem_final_bound_on_circle0 (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ) (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
norm (f z) ≤ (2 * r / (R - r)) * M := by
                                                                                     
  have h_ineq : R * norm (f z) ≤ r * norm (2 * M - f z) :=
    lem_f_bound_rearranged R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

  have h_bound : norm (f z) ≤ (2 * M * r) / (R - r) :=
    lem_rtriangle7 r R M (f z) hr_pos hr_lt_R hM h_ineq

  have h_rearrange : (2 * M * r) / (R - r) = (2 * r / (R - r)) * M := by
    field_simp

  rw [← h_rearrange]
  exact h_bound

lemma lem_final_bound_on_circle (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ) (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
norm (f z) ≤ (2 * r / (R - r)) * M := by
  exact lem_final_bound_on_circle0 R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

lemma lem_BCI (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_in_ball : norm z ≤ r) :
norm (f z) ≤ (2 * r / (R - r)) * M := by
                                  
  let B := (2 * r / (R - r)) * M

  have hB : B ≥ 0 := by
    unfold B
    apply mul_nonneg
    · apply div_nonneg
      · apply mul_nonneg
        · norm_num
        · linarith [hr_pos]
      · linarith [hr_lt_R]
    · linarith [hM]

  have h_analytic_r : AnalyticOn ℂ f (closure (ballDR r)) := by
    apply AnalyticOn.mono h_analytic
                                                   
    apply closure_mono
    unfold ballDR
    exact Metric.ball_subset_ball (le_of_lt hr_lt_R)

  have hz_in_closure_r : z ∈ closure (ballDR r) := by
    rw [lem_ballDR r hr_pos]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    exact hz_in_ball

  have h_boundary : ∀ w : ℂ, norm w = r → norm (f w) ≤ B := by
    intro w hw_boundary
    exact lem_final_bound_on_circle R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R w hw_boundary

  have h_closure := (lem_MMP r B hr_pos hB f h_analytic_r).mpr h_boundary

  exact h_closure z hz_in_closure_r

theorem thm_BorelCaratheodoryI (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R) :
sSup ((norm ∘ f) '' (closure (ballDR r))) ≤ (2 * r / (R - r)) * M := by
                                                                                               
  apply Real.sSup_le
  ·                                                                                                      
    intro x hx

    obtain ⟨z, hz_in_closure, hx_eq⟩ := hx
    rw [← hx_eq]

    have hz_bound : norm z ≤ r := by
      rw [lem_ballDR r hr_pos] at hz_in_closure
      rw [Metric.mem_closedBall] at hz_in_closure
      rw [Complex.dist_eq] at hz_in_closure
      simp at hz_in_closure
      exact hz_in_closure
                    
    exact lem_BCI R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_bound
  ·                                       
    apply mul_nonneg
    · apply div_nonneg
      · apply mul_nonneg
        · norm_num
        · linarith [hr_pos]
      · linarith [hr_lt_R]
    · linarith [hM]


lemma cauchy_formula_deriv {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (_h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r_int), (w - z)⁻¹ ^ 2 • f w := by
                                       
  obtain ⟨U', hU'_open, h_subset, hf_diff_U'⟩ := hf_domain

  have hz_in_ball : z ∈ Metric.ball (0 : ℂ) r_int := by
    apply Metric.mem_ball.mpr
    have h1 : ‖z - 0‖ ≤ r_z := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz
    simp only [sub_zero] at h1
    have h2 : ‖z‖ < r_int := lt_of_le_of_lt h1 h_r_z_lt_r_int
    rwa [dist_eq_norm, sub_zero]

  set U := Metric.ball (0 : ℂ) R_analytic

  have hc_subset : Metric.closedBall (0 : ℂ) r_int ⊆ U := by
    apply Metric.closedBall_subset_ball
    exact h_r_int_lt_R_analytic

  have hf_on_U : DifferentiableOn ℂ f U := by

    apply DifferentiableOn.mono hf_diff_U'
    calc U = Metric.ball 0 R_analytic := rfl
         _ ⊆ Metric.closedBall 0 R_analytic := Metric.ball_subset_closedBall
         _ ⊆ U' := h_subset

  have cauchy_eq := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
    Metric.isOpen_ball hc_subset hf_on_U hz_in_ball

  rw [← cauchy_eq]

  congr 2
  ·                                         
    simp only [one_div]
                                  
    rfl
  ·                                               
    ext w
    rw [← inv_pow]


lemma circleMap_zero_eq_exp (r : ℝ) (t : ℝ) : circleMap 0 r t = r * Complex.exp (I * t) := by
                                                                         
  rw [circleMap]
                                                                                    
  simp only [zero_add]
                                                                          
  congr 2
  rw [mul_comm (t : ℂ) Complex.I]
                                      
  rfl

lemma deriv_ofReal_eq_one (t : ℝ) : deriv Complex.ofReal t = 1 := by

  have h : deriv Complex.ofReal t = Complex.ofReal 1 := by

    rw [show Complex.ofReal = ⇑Complex.ofRealCLM from rfl]
    exact ContinuousLinearMap.deriv Complex.ofRealCLM
                                       
  rw [h]
  simp only [Complex.ofReal_one]

lemma differentiableAt_ofReal (t : ℝ) : DifferentiableAt ℝ Complex.ofReal t := by
                                                                                
  rw [show Complex.ofReal = ⇑Complex.ofRealCLM from rfl]
                                                                                    
  apply ContinuousLinearMap.differentiableAt

lemma lem_dw_dt_real {r_int : ℝ} (t : ℝ) :
deriv (fun (t' : ℝ) => r_int * Complex.exp (I * t')) t = I * r_int * Complex.exp (I * t) := by
                                       
  rw [deriv_const_mul]
                                             
  rw [deriv_cexp]
                                                  
  rw [deriv_const_mul]
                                                            
  rw [deriv_ofReal_eq_one]
                                                                                        
  ring
                                                                         
  · exact differentiableAt_ofReal t
  · exact (differentiableAt_const I).mul (differentiableAt_ofReal t)
  · exact DifferentiableAt.cexp ((differentiableAt_const I).mul (differentiableAt_ofReal t))

lemma deriv_circleMap_zero (r : ℝ) (t : ℝ) : deriv (circleMap 0 r) t = I * r * Complex.exp (I * t) := by
                                                            
  have h : circleMap 0 r = fun (t' : ℝ) => r * Complex.exp (I * t') := by
    ext t'
    exact circleMap_zero_eq_exp r t'

  rw [h]

  exact lem_dw_dt_real t

lemma lem_CIF_deriv_param {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    deriv f z = (1 / (2 * Real.pi * I)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(I * r_int * Complex.exp (I * t) * ((r_int * Complex.exp (I * t)) - z)⁻¹ ^ 2) * f (r_int * Complex.exp (I * t))) := by
                                                               
  rw [cauchy_formula_deriv hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

  rw [circleIntegral_def_Icc]

  rw [smul_eq_mul]

  simp only [circleMap_zero_eq_exp, deriv_circleMap_zero]

  congr 2
  ext t
  simp only [smul_eq_mul]
  ring


lemma complex_coeff_I_cancel : (1 : ℂ) / (2 * Real.pi * I) * I = 1 / (2 * Real.pi) := by
  field_simp [I, Complex.I_ne_zero, Real.pi_pos.ne']

lemma factor_I_from_integrand (f : ℂ → ℂ) (r_int : ℝ) (z : ℂ) :
  ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I * ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
  I * ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) := by

  have h : ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I * ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
           ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I • (↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t))) := by
    congr 1
    ext t
    rw [smul_eq_mul]
    ring
  rw [h]
                                                              
  rw [MeasureTheory.integral_smul]
                                                                 
  rw [smul_eq_mul]

lemma integrand_transform_div (f : ℂ → ℂ) (r_int : ℝ) (z : ℂ) (t : ℝ) :
  ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
  ↑r_int * Complex.exp (I * ↑t) * f (↑r_int * Complex.exp (I * ↑t)) / (↑r_int * Complex.exp (I * ↑t) - z) ^ 2 := by
                                                              
  rw [inv_pow]
                                                                                     
  rw [← div_eq_mul_inv]
                                                
  ring

lemma lem_CIF_deriv_simplified {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    deriv f z = (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) := by
                              
  rw [lem_CIF_deriv_param hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

  rw [factor_I_from_integrand f r_int z]

  rw [← mul_assoc, complex_coeff_I_cancel]

  congr 2
  funext t
  rw [integrand_transform_div f r_int z t]

lemma lem_modulus_of_f_prime0 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm (deriv f z) = norm ((1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
                                                                 
  rw [lem_CIF_deriv_simplified hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

lemma one_div_two_pi_pos : (1 : ℝ) / (2 * Real.pi) > 0 := by
                            
  have h_pi_pos : Real.pi > 0 := Real.pi_pos
                        
  have h_2pi_pos : 2 * Real.pi > 0 := by
    apply mul_pos
    · norm_num
    · exact h_pi_pos
                              
  apply div_pos
  · norm_num
  · exact h_2pi_pos

lemma abs_integral_le_integral_abs {a b : ℝ} {g : ℝ → ℂ} (_hab : a ≤ b) : norm (∫ (t : ℝ) in Set.Icc a b, g t) ≤ ∫ (t : ℝ) in Set.Icc a b, norm (g t) := by

  exact MeasureTheory.norm_integral_le_integral_norm g


lemma complex_abs_mul (a b : ℂ) : norm (a * b) = norm a * norm b :=
  Complex.norm_mul a b

lemma complex_abs_ofReal_nonneg (r : ℝ) (hr : r ≥ 0) : norm (↑r : ℂ) = r := by
                                          
  have h1 : norm (↑r * 1) = r * norm (1 : ℂ) := by simp; assumption
                                         
  simp only [mul_one] at h1
  have h2 : norm (1 : ℂ) = 1 := by simp
  rw [h2] at h1
  simp only [mul_one] at h1
  simp
  assumption

lemma abs_one_div_two_pi_complex : norm (1 / (2 * ↑Real.pi : ℂ)) = 1 / (2 * Real.pi) := by
                                                                              
  have h_eq : (1 / (2 * ↑Real.pi) : ℂ) = ↑(1 / (2 * Real.pi) : ℝ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]

  rw [h_eq]

  have h_nonneg : (1 / (2 * Real.pi) : ℝ) ≥ 0 := by
    apply div_nonneg
    · norm_num
    · apply mul_nonneg
      · norm_num
      · exact le_of_lt Real.pi_pos

  exact complex_abs_ofReal_nonneg (1 / (2 * Real.pi)) h_nonneg

lemma lem_integral_modulus_inequality {r_int : ℝ} {z : ℂ} {f : ℂ → ℂ} :
norm ((1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), (r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) ≤ (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
                                                        
  rw [complex_abs_mul]

  rw [abs_one_div_two_pi_complex]

  apply mul_le_mul_of_nonneg_left
  ·                                                                  
    have h_2pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := by
      apply mul_nonneg
      · norm_num
      · exact le_of_lt Real.pi_pos
    exact abs_integral_le_integral_abs h_2pi_nonneg
  · exact le_of_lt one_div_two_pi_pos

lemma lem_modulus_of_f_prime {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm (deriv f z) ≤ (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
                                                           
  rw [lem_modulus_of_f_prime0 hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]
                                                                        
  exact lem_integral_modulus_inequality

lemma lem_modulus_of_integrand_product2 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (_hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (_h_r_z_pos : 0 < r_z)
    (_h_r_z_lt_r_int : r_z < r_int)
    (_h_r_int_lt_R_analytic : r_int < R_analytic) :
    norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) =
norm (f (r_int * Complex.exp (I * t))) * norm (r_int * Complex.exp (I * t)) := by
                                                                     
  rw [norm_mul]

lemma lem_modeit (t : ℝ) : norm (Complex.exp (I * t)) = Real.exp (Complex.re (I * t)) := by
                                                        
  exact Complex.norm_exp (I * t)

lemma lem_Reit0 (t : ℝ) : Complex.re (I * t) = 0 := by
                                        
  unfold I
                                                    
  rw [Complex.mul_re]

  rw [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
                                  
  ring


lemma lem_e01 : Real.exp 0 = 1 := by
  exact Real.exp_zero


lemma lem_modulus_of_e_it_is_one (t : ℝ) : norm (Complex.exp (I * t)) = 1 := by
                                                                                            
  rw [lem_modeit]
                                                   
  rw [lem_Reit0]
                                         
  rw [lem_e01]

lemma lem_modulus_of_ae_it {a t : ℝ} (ha : 0 < a) : norm (a * Complex.exp (I * t)) = a := by
                                                              
  rw [norm_mul, lem_modulus_of_e_it_is_one, mul_one, Complex.norm_real]
  exact abs_of_pos ha

lemma lem_modulus_of_integrand_product3 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic) :
norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) = r_int * norm (f (r_int * Complex.exp (I * t))) := by
                                                                      
  rw [lem_modulus_of_integrand_product2 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic]
                                                                            
  have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
  rw [lem_modulus_of_ae_it h_r_int_pos]
                                                                
  ring


lemma lem_modulus_wz (w z : ℂ) : norm ((w - z) ^ 2) = (norm (w - z)) ^ 2 := by
                                     
  exact Complex.norm_pow (w - z) 2

lemma lem_reverse_triangle (w z : ℂ) : norm w - norm z ≤ norm (w - z) := by

  exact norm_sub_norm_le w z


lemma lem_reverse_triangle3 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (_h_r_int_lt_R_analytic : r_int < R_analytic) :
r_int - norm z ≤ norm (r_int * Complex.exp (I * t) - z) := by
                                                  
  have h_mod : norm (r_int * Complex.exp (I * t)) = r_int := by
    have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
    exact lem_modulus_of_ae_it h_r_int_pos
                                                                    
  have h_triangle := lem_reverse_triangle (r_int * Complex.exp (I * t)) z
                                     
  rw [h_mod] at h_triangle
  exact h_triangle

lemma lem_zrr1 {R_analytic r_z r_int : ℝ}
    (_h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (_h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
0 < r_int - norm z := by
                                                      
  have h1 : dist z 0 ≤ r_z := Metric.mem_closedBall.mp hz
                                        
  have h2 : dist z 0 = ‖z‖ := by
    rw [dist_eq_norm, sub_zero]
                 
  have h3 : ‖z‖ ≤ r_z := by rwa [← h2]
                                      
  have h4 : norm z = ‖z‖ := rfl
                    
  have h5 : norm z ≤ r_z := by rwa [h4]
                                                     
  have h6 : norm z < r_int := lt_of_le_of_lt h5 h_r_z_lt_r_int
                                 
  linarith

lemma lem_zrr2 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
r_int - r_z ≤ norm (r_int * Complex.exp (I * t) - z) := by
                                                        
  have h1 : norm z ≤ r_z := by
    have h_dist : dist z 0 ≤ r_z := Metric.mem_closedBall.mp hz
    rw [dist_eq_norm, sub_zero] at h_dist
    exact h_dist
                                                             
  have h2 : r_int - r_z ≤ r_int - norm z := by linarith [h1]
                                                                                               
  have h3 := @lem_reverse_triangle3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic
                               
  exact le_trans h2 h3



lemma lem_zrr3 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
(r_int - r_z) ^ 2 ≤ norm (r_int * Complex.exp (I * t) - z) ^ 2 := by
                                                       
  have h_ineq := @lem_zrr2 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                    
  have h_nonneg_left : 0 ≤ r_int - r_z := by linarith [h_r_z_lt_r_int]
  have h_nonneg_right : 0 ≤ norm (r_int * Complex.exp (I * t) - z) := norm_nonneg _
                                                    
  have h_sq := mul_self_le_mul_self h_nonneg_left h_ineq
                                
  rw [pow_two, pow_two]
  exact h_sq


lemma lem_reverse_triangle4 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
0 < norm (r_int * Complex.exp (I * t) - z) := by
                                             
  have h1 := lem_zrr1 h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                                               
  have h2 := @lem_reverse_triangle3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic
                               
  exact lt_of_lt_of_le h1 h2

lemma lem_wposneq0 (w : ℂ) : norm w > 0 → w ≠ 0 := by
  intro h
                                                  
  by_contra h_eq_zero
                              
  have h_abs_zero : norm w = 0 := by
    rw [h_eq_zero]
    simp
                                        
  rw [h_abs_zero] at h
  exact lt_irrefl 0 h

lemma lem_reverse_triangle5 {R_analytic r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
r_int * Complex.exp (I * t) - z ≠ 0 := by
                                                                                  
  have h_pos := @lem_reverse_triangle4 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                  
  exact lem_wposneq0 (r_int * Complex.exp (I * t) - z) h_pos

lemma lem_reverse_triangle6 {R_analytic r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
(r_int * Complex.exp (I * t) - z) ^ 2 ≠ 0 := by
                                                                   
  have h_ne_zero := lem_reverse_triangle5 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                                    
  exact pow_ne_zero 2 h_ne_zero

lemma lem_absdiv {a b : ℂ} (_hb : b ≠ 0) : norm (a / b) = norm a / norm b := by
                                             
  exact norm_div a b

lemma lem_modulus_of_integrand_product {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (_hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2 := by
                                               
  have h_neq_zero : r_int * Complex.exp (I * t) - z ≠ 0 :=
    lem_reverse_triangle5 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                         
  have h_sq_neq_zero : (r_int * Complex.exp (I * t) - z) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_self_ne_zero.mpr h_neq_zero
                                              
  rw [lem_absdiv h_sq_neq_zero]
                                                              
  rw [lem_modulus_wz]

lemma lem_modulus_of_product {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
(r_int * norm (f (r_int * Complex.exp (I * t)))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2 := by
                                                                                             
  rw [lem_modulus_of_integrand_product t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]
                                                                           
  rw [lem_modulus_of_integrand_product3 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic]



lemma lem_modulus_of_product4 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤
(r_int * norm (f (r_int * Complex.exp (I * t)))) / ((r_int - r_z) ^ 2) := by
                                               
  rw [lem_modulus_of_product t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

  have h_ineq := @lem_zrr3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  apply div_le_div_of_nonneg_left
  ·                            
    apply mul_nonneg
    · linarith [h_r_z_pos, h_r_z_lt_r_int]
    · exact norm_nonneg _
  ·                                           
    apply pow_pos
    linarith [h_r_z_lt_r_int]
  ·                                                              
    exact h_ineq

lemma lem_bound_on_f_at_r_prime {M R_analytic r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (hr_int_pos : 0 < r_int)
    (hr_int_lt_R_analytic : r_int < R_analytic)
    (f : ℂ → ℂ)

    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ z ∈ Metric.closedBall 0 R_analytic, (f z).re ≤ M)
    (t : ℝ) :
norm (f (r_int * Complex.exp (I * t))) ≤ (2 * r_int * M) / (R_analytic - r_int) := by
                                         
  obtain ⟨U, hU_open, h_subset, hf_diff_U⟩ := hf_domain

  let z₀ := r_int * Complex.exp (I * t)

  have h_sSup_bound := thm_BorelCaratheodoryI R_analytic M hR_analytic_pos hM_pos f
                                                                   
    (by
                                        
      have h_analytic_U : AnalyticOn ℂ f U := hf_diff_U.analyticOn hU_open

      rw [ballDR]
      convert (preTransparency := .instances) h_analytic_U.mono h_subset
                                                                              
      apply closure_ball
      linarith
      )
    hf0
    (by rwa [lem_ballDR R_analytic hR_analytic_pos])                         
    r_int hr_int_pos hr_int_lt_R_analytic

  have hz₀_in_ball : z₀ ∈ Metric.closedBall 0 r_int := by
    rw [Metric.mem_closedBall]
    simp only [dist_eq_norm, sub_zero]
                                                          
    have h_norm : ‖r_int * Complex.exp (I * t)‖ = r_int := by
      rw [norm_mul]

      have h1 : ‖(r_int : ℂ)‖ = r_int := by
        rw [Complex.norm_real]
        exact abs_of_pos hr_int_pos
                                           
      have h2 : ‖Complex.exp (I * ↑t)‖ = 1 := by
                                                               
        exact lem_modulus_of_e_it_is_one t
      rw [h1, h2]
      ring
    rw [h_norm]

  have hz₀_in_closure : z₀ ∈ closure (ballDR r_int) := by
    rw [lem_ballDR r_int hr_int_pos]
    exact hz₀_in_ball

  have h_in_image : norm (f z₀) ∈ (norm ∘ f) '' (closure (ballDR r_int)) := by
    use z₀, hz₀_in_closure
    rfl

  have h_le_sSup : norm (f z₀) ≤ sSup ((norm ∘ f) '' (closure (ballDR r_int))) := by
    apply le_csSup
                                            
    · use (2 * r_int / (R_analytic - r_int)) * M
      intros x hx
      obtain ⟨w, hw_in, hx_eq⟩ := hx
      rw [← hx_eq]
                                         
      have hw_in_closed : w ∈ Metric.closedBall 0 r_int := by
        rwa [← lem_ballDR r_int hr_int_pos]
                                                                   
      have hw_in_R : w ∈ Metric.closedBall 0 R_analytic := by
        have h_subset : Metric.closedBall (0 : ℂ) r_int ⊆ Metric.closedBall 0 R_analytic := by
          apply Metric.closedBall_subset_closedBall
          linarith [hr_int_lt_R_analytic]
        exact h_subset hw_in_closed
                                                  
      exact lem_BCI R_analytic M hR_analytic_pos hM_pos f
        (by
          rw [ballDR]
          have h_analytic_U : AnalyticOn ℂ f U := hf_diff_U.analyticOn hU_open
          convert (preTransparency := .instances) h_analytic_U.mono h_subset
          apply closure_ball
          linarith)
        hf0
        (by rwa [lem_ballDR R_analytic hR_analytic_pos])
        r_int hr_int_pos hr_int_lt_R_analytic w
        (by aesop)
                                
    · exact h_in_image

  calc norm (f z₀)
    ≤ sSup ((norm ∘ f) '' (closure (ballDR r_int))) := h_le_sSup
    _ ≤ (2 * r_int / (R_analytic - r_int)) * M := h_sSup_bound
    _ = (2 * r_int * M) / (R_analytic - r_int) := by ring

lemma lem_bound_on_integrand_modulus {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z)
    (t : ℝ) :
norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
                                                            
  have h1 := lem_modulus_of_product4 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                 
  have h2 := lem_bound_on_f_at_r_prime hM_pos hR_analytic_pos (lt_trans h_r_z_pos h_r_z_lt_r_int) h_r_int_lt_R_analytic f hf_domain hf0 hRe_f_le_M t

  have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
  have h_denom_nonneg : 0 ≤ (r_int - r_z) ^ 2 := by
    apply sq_nonneg

  have h3 : (r_int * norm (f (r_int * Complex.exp (I * t)))) / (r_int - r_z) ^ 2 ≤
            (r_int * (2 * r_int * M / (R_analytic - r_int))) / (r_int - r_z) ^ 2 := by
    apply div_le_div_of_nonneg_right _ h_denom_nonneg
    apply mul_le_mul_of_nonneg_left h2
    linarith [h_r_int_pos]

  have h4 : (r_int * (2 * r_int * M / (R_analytic - r_int))) / (r_int - r_z) ^ 2 =
            (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
    have h_R_sub_r_pos : 0 < R_analytic - r_int := by linarith [h_r_int_lt_R_analytic]
    have h_r_sub_r_pos : 0 < r_int - r_z := by linarith [h_r_z_lt_r_int]
    field_simp [ne_of_gt h_R_sub_r_pos, ne_of_gt (pow_pos h_r_sub_r_pos 2)]

  rw [h4] at h3
  exact le_trans h1 h3

lemma lem_integral_inequality_aux {g : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (h_integrable : IntervalIntegrable g MeasureTheory.volume a b)
    (h_bound : ∀ t ∈ Set.Icc a b, g t ≤ C) :
∫ t in a..b, g t ≤ ∫ _t in a..b, C := by

  have h_const_integrable : IntervalIntegrable (fun _ => C) MeasureTheory.volume a b :=
    intervalIntegrable_const
                                                                             
  have h_pointwise : ∀ x ∈ Set.Icc a b, g x ≤ (fun _ => C) x := by
    intro x hx
    simp
    exact h_bound x hx
                                   
  exact intervalIntegral.integral_mono_on hab h_integrable h_const_integrable h_pointwise

lemma lem_integral_inequality {g : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (h_integrable : IntervalIntegrable g MeasureTheory.volume a b)
    (h_bound : ∀ t ∈ Set.Icc a b, g t ≤ C) :
∫ t in Set.Icc a b, g t ≤ ∫ _t in Set.Icc a b, C := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab]
  exact lem_integral_inequality_aux hab h_integrable h_bound

lemma continuous_real_parameterization (r : ℝ) : Continuous (fun t : ℝ => r * Complex.exp (I * t)) := by

  have h1 : Continuous (fun t : ℝ => (t : ℂ)) := Complex.continuous_ofReal

  have h2 : Continuous (fun z : ℂ => I * z) := by
    apply Continuous.mul
    · exact continuous_const
    · exact continuous_id

  have h3 : Continuous Complex.exp := Complex.continuous_exp

  have h4 : Continuous (fun z : ℂ => (r : ℂ) * z) := by
    apply Continuous.mul
    · exact continuous_const
    · exact continuous_id

  apply Continuous.comp h4
  apply Continuous.comp h3
  apply Continuous.comp h2
  exact h1

lemma continuous_f_parameterized {f : ℂ → ℂ} {R r : ℝ}     (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
 (hr_pos : 0 < r) (hr_lt_R : r < R) : Continuous (fun t : ℝ => f (r * Complex.exp (I * t))) := by
                                                                       
  obtain ⟨U', hU'_open, h_subset, hf_diff_U'⟩ := hf_domain
  have hf_cont : ContinuousOn f (Metric.closedBall 0 R) := by
                                                                  
    have hf_on_closed : DifferentiableOn ℂ f (Metric.closedBall 0 R) :=
      hf_diff_U'.mono h_subset
                                                               
    exact DifferentiableOn.continuousOn hf_on_closed

  have hparam_cont : Continuous (fun t : ℝ => r * Complex.exp (I * t)) := continuous_real_parameterization r

  have hparam_range : ∀ t : ℝ, r * Complex.exp (I * t) ∈ Metric.closedBall 0 R := by
    intro t
    rw [Metric.mem_closedBall, dist_zero_right]
                                                        
    change norm (r * Complex.exp (I * t)) ≤ R
    rw [lem_modulus_of_ae_it hr_pos]
    exact le_of_lt hr_lt_R

  have hcomp_on : ContinuousOn (fun t : ℝ => f (r * Complex.exp (I * t))) Set.univ := by
    apply ContinuousOn.comp hf_cont (Continuous.continuousOn hparam_cont)
    intro t _
    exact hparam_range t

  exact continuousOn_univ.mp hcomp_on

lemma continuous_denominator_parameterized (r : ℝ) (z : ℂ) : Continuous (fun t : ℝ => (r * Complex.exp (I * t) - z) ^ 2) := by

  have h1 : Continuous (fun t : ℝ => r * Complex.exp (I * t) - z) := by
                                                         
    apply Continuous.sub
    ·                                                                                 
      exact continuous_real_parameterization r
    ·                                           
      exact continuous_const

  have h2 : Continuous (fun x : ℂ => x ^ 2) := continuous_pow 2

  exact Continuous.comp h2 h1

lemma interval_integrable_cauchy_integrand {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} {z : ℂ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
IntervalIntegrable (fun t => norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) MeasureTheory.volume 0 (2 * Real.pi) := by
                                                             
  apply Continuous.intervalIntegrable

  apply Continuous.comp continuous_norm

  apply Continuous.div₀

  · apply Continuous.mul
                                                     
    · exact continuous_real_parameterization r_int
                                                         
    · have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
      exact continuous_f_parameterized hf_domain h_r_int_pos h_r_int_lt_R_analytic

  · exact continuous_denominator_parameterized r_int z

  · intro t
    exact lem_reverse_triangle6 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

lemma integral_const_over_interval (C : ℝ) :
∫ _t in Set.Icc 0 (2 * Real.pi), C = (2 * Real.pi) * C := by
                                                                             
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
                                                                                     
  have h_le : (0 : ℝ) ≤ 2 * Real.pi := by
    apply mul_nonneg
    · norm_num
    · exact Real.pi_pos.le
  rw [← intervalIntegral.integral_of_le h_le]
                                                 
  rw [intervalIntegral.integral_const]
                                                        
  simp [sub_zero, smul_eq_mul]

lemma lem_f_prime_bound_by_integral_of_constant {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
norm (deriv f z) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
                                                                 
  have h1 := lem_modulus_of_f_prime hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  set C := (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2)

  have h_bound : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ C := by
    intro t ht
    exact lem_bound_on_integrand_modulus hM_pos hR_analytic_pos h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hf_domain hf0 hRe_f_le_M hz t

  have h_eq : ∀ t, norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) := by
    intro t
    congr 2
    ring

  have h_bound_h1 : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
    norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ C := by
    intro t ht
    rw [h_eq]
    exact h_bound t ht

  have h_integrable : IntervalIntegrable (fun t => norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) MeasureTheory.volume 0 (2 * Real.pi) := by
                                            
    exact interval_integrable_cauchy_integrand hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  have h2 := lem_integral_inequality ?_ h_integrable h_bound_h1

  have h_const_integral : ∫ t in Set.Icc 0 (2 * Real.pi), C = (2 * Real.pi) * C := by
                                                       
    exact integral_const_over_interval C

  rw [h_const_integral] at h2

  have h3 : (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
    norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) ≤
    (1 / (2 * Real.pi)) * (2 * Real.pi * C) := by
    apply mul_le_mul_of_nonneg_left h2
    apply div_nonneg
    · norm_num
    · linarith [Real.pi_pos]

  have h4 : (1 / (2 * Real.pi)) * (2 * Real.pi * C) = C := by
    have h_pi_ne_zero : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (by linarith [Real.pi_pos])
    field_simp [h_pi_ne_zero]

  rw [h4] at h3
  exact le_trans h1 h3
  simp [Real.pi_nonneg]



lemma lem_f_prime_bound {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
norm (deriv f z) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
                                              
  exact lem_f_prime_bound_by_integral_of_constant hM_pos hR_analytic_pos h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hf_domain hf0 hRe_f_le_M hz


lemma lem_r_prime_lt_R {r R : ℝ}
    (_h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
(r + R) / 2 < R := by
                                                                  
  rw [add_div_two_lt_right]
  exact h_r_lt_R

lemma lem_r_prime_is_intermediate {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
r < (r + R) / 2 ∧ (r + R) / 2 < R := by
  constructor
  ·                         
    rw [left_lt_add_div_two]
    exact h_r_lt_R
  ·                         
    exact lem_r_prime_lt_R h_r_pos h_r_lt_R

lemma lem_calc_R_minus_r_prime {r R : ℝ}
    (_h_r_pos : 0 < r)
    (_h_r_lt_R : r < R) :
R - ((r + R) / 2) = (R - r) / 2 := by
  field_simp; ring


lemma lem_calc_denominator_specific {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
(R - ((r + R) / 2)) * (((r + R) / 2) - r) ^ 2 = ((R - r) ^ 3) / 8 := by
                                                           
  rw [lem_calc_R_minus_r_prime h_r_pos h_r_lt_R]
                                              
  have h_calc : ((r + R) / 2) - r = (R - r) / 2 := by
    field_simp; ring
                                
  rw [h_calc]

  ring

lemma lem_calc_numerator_specific {M r R : ℝ}
    (_hM_pos : 0 < M)
    (_hr_pos : 0 < r)
    (_hr_lt_R : r < R) :
2 * (((r + R) / 2) ^ 2) * M = ((R + r) ^ 2 * M) / 2 := by
                                                  
  ring

lemma lem_frac_simplify {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) = (((R + r) ^ 2 * M) / 2) / (((R - r) ^ 3) / 8) := by
                                     
  dsimp only
                              
  have h_num := lem_calc_numerator_specific hM_pos hr_pos hr_lt_R
                                
  have h_denom := lem_calc_denominator_specific hr_pos hr_lt_R
                              
  rw [← h_num, ← h_denom]

lemma lem_frac_simplify2 {M r R : ℝ}
    (hM_pos : 0 < M)
    (_hr_pos : 0 < r)
    (hr_lt_R : r < R) :
((R + r) ^ 2 * M / 2) / ((R - r) ^ 3 / 8) = (4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) := by

  have h_two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
  have h_eight_ne_zero : (8 : ℝ) ≠ 0 := by norm_num
  have h_R_minus_r_ne_zero : R - r ≠ 0 := by linarith [hr_lt_R]
  have h_R_minus_r_pow_ne_zero : (R - r) ^ 3 ≠ 0 := by
    apply pow_ne_zero
    exact h_R_minus_r_ne_zero

  field_simp [h_two_ne_zero, h_eight_ne_zero, h_R_minus_r_pow_ne_zero]; ring

lemma lem_frac_simplify3 {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) = (4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) := by
                              
  dsimp only
                                                         
  have h1 := lem_frac_simplify hM_pos hr_pos hr_lt_R
                                                            
  have h2 := lem_frac_simplify2 hM_pos hr_pos hr_lt_R
                          
  rw [h1, h2]

lemma lem_ineq_R_plus_r_lt_2R {r R : ℝ} (h_r_lt_R : r < R) :
R + r < 2 * R := by
                           
  rw [two_mul]
                                                                
  linarith [h_r_lt_R]

lemma lem_R_plus_r_is_positive {r R : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
0 < R + r := by
                                         
  have hR_pos : 0 < R := lt_trans hr_pos hr_lt_R
                                       
  exact add_pos hR_pos hr_pos


lemma lem_square_inequality_strict {a b : ℝ}
    (h_a_pos : 0 < a)
    (h_a_lt_b : a < b) :
a ^ 2 < b ^ 2 := by
                             
  have h_a_nonneg : 0 ≤ a := le_of_lt h_a_pos
                                                    
  have h_b_pos : 0 < b := lt_trans h_a_pos h_a_lt_b
  have h_b_nonneg : 0 ≤ b := le_of_lt h_b_pos
                                   
  have h_squares := mul_self_lt_mul_self_iff h_a_nonneg h_b_nonneg
                                                     
  have h_mult : a * a < b * b := h_squares.mp h_a_lt_b
                                                   
  rw [← pow_two, ← pow_two] at h_mult
  exact h_mult


lemma lem_2R_sq_is_4R_sq {R : ℝ} (_hR_pos : 0 < R) : (2 * R) ^ 2 = 4 * R ^ 2 := by
                                                  
  ring

lemma lem_ineq_R_plus_r_sq {r R : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
(R + r) ^ 2 < 4 * R ^ 2 := by
                      
  have h1 := lem_ineq_R_plus_r_lt_2R hr_lt_R
                  
  have h2 := lem_R_plus_r_is_positive hr_pos hr_lt_R
                                                                    
  have h3 := lem_square_inequality_strict h2 h1
                                                          
  have hR_pos : 0 < R := lt_trans hr_pos hr_lt_R
  have h4 := lem_2R_sq_is_4R_sq hR_pos
  rw [h4] at h3
  exact h3

lemma lem_ineq_R_plus_r_sqM {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
4 * (R + r) ^ 2 * M < 16 * R ^ 2 * M := by
                                                              
  have h_ineq := lem_ineq_R_plus_r_sq hr_pos hr_lt_R
                        
  have h_4M_pos : 0 < 4 * M := by
    apply mul_pos
    · norm_num
    · exact hM_pos
                                 
  have h_mult := mul_lt_mul_of_pos_right h_ineq h_4M_pos
                                      
  nlinarith [h_mult]

lemma lem_simplify_final_bound {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
(4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) < (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
                                                                
  have h_num_ineq := lem_ineq_R_plus_r_sqM hM_pos hr_pos hr_lt_R
                            
  have h_denom_pos : 0 < (R - r) ^ 3 := by
    apply pow_pos
    linarith [hr_lt_R]
                                
  exact div_lt_div_of_pos_right h_num_ineq h_denom_pos

lemma lem_bound_after_substitution {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) ≤ (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
                           
  dsimp only
                                                      
  have h1 := lem_frac_simplify3 hM_pos hr_pos hr_lt_R
                                 
  dsimp only at h1
  rw [h1]
                                                            
  have h2 := lem_simplify_final_bound hM_pos hr_pos hr_lt_R
                                  
  exact le_of_lt h2

theorem borel_caratheodory_II {f : ℂ → ℂ} {R M r : ℝ}
    (hR_pos : 0 < R)
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r) :
norm (deriv f z) ≤ (16 * M * R ^ 2) / ((R - r) ^ 3) := by
                                                            
  set r_prime := (r + R) / 2

  have h_intermediate := lem_r_prime_is_intermediate hr_pos hr_lt_R
  have h_r_lt_r_prime := h_intermediate.1
  have h_r_prime_lt_R := h_intermediate.2

  have h_bound := lem_f_prime_bound hM_pos hR_pos hr_pos h_r_lt_r_prime h_r_prime_lt_R hf_domain hf0 hRe_f_le_M hz

  have h_final := lem_bound_after_substitution hM_pos hr_pos hr_lt_R

  have h_combined : norm (deriv f z) ≤ (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
    exact le_trans h_bound h_final

  convert (preTransparency := .instances) h_combined using 1
  ring

open _root_.Complex _root_.MeasureTheory _root_.intervalIntegral
open scoped _root_.Interval











































open _root_.Filter _root_.Topology



















open _root_.Classical
                                                                                      

















open scoped _root_.Topology






























end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT2_LogDerivative
namespace Erdos970




open _root_.Filter _root_.Metric _root_.Set _root_.Bornology _root_.Function


open _root_.Classical

lemma lem_frho_zero (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (_hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    f ρ = 0 := h_rho_in_KfR1.2

lemma lem_m_rho_is_nat (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (_h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≠ ⊤ := by
  intro ρ h_rho_in_KfR1
                                           
  have hρ_closed_R1 : ρ ∈ Metric.closedBall (0 : ℂ) R1 := h_rho_in_KfR1.1
                                    
  have hR1_le_R : R1 ≤ R := by linarith
  have hR1_lt_one : R1 < 1 := by linarith
                       
  have hρ_ball1 : ρ ∈ Metric.ball (0 : ℂ) 1 := by
    have hdist_le : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_closed_R1)
    have hdist_lt : dist ρ (0 : ℂ) < 1 := by linarith
    simpa [Metric.mem_ball] using hdist_lt
                       
  have hf_at_ρ : AnalyticAt ℂ f ρ := by
                                      
    have hsubset : Metric.closedBall (0 : ℂ) R1 ⊆ Metric.closedBall (0 : ℂ) 1 :=
      Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_one)
    have hρ_closed1 : ρ ∈ Metric.closedBall (0 : ℂ) 1 := hsubset hρ_closed_R1
    exact h_f_analytic ρ hρ_closed1
                                                    
  by_contra htop
                                                           
  have h_eventually_zero : ∀ᶠ z in nhds ρ, f z = 0 := by
    have h_equiv : (analyticOrderAt f ρ = ⊤ ↔ ∀ᶠ z in nhds ρ, f z = 0) := by
      simp [analyticOrderAt, hf_at_ρ]
    exact h_equiv.mp (by simpa using htop)
                                                     
  have hf_on_ball : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      (Metric.ball_subset_closedBall : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1) hz
    exact h_f_analytic z hz'
                                  
  have h_preconn : IsPreconnected (Metric.ball (0 : ℂ) 1) :=
    (Metric.isConnected_ball (by exact (zero_lt_one : (0 : ℝ) < 1))).isPreconnected
                                                  
  have h_eqOn_zero : Set.EqOn f 0 (Metric.ball (0 : ℂ) 1) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf_on_ball h_preconn hρ_ball1
      h_eventually_zero
                                 
  have h0_in_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simp [Metric.mem_ball]
  have : f 0 = 0 := by
    have h := h_eqOn_zero h0_in_ball
    simpa [Pi.zero_apply] using h
  exact h_f_nonzero_at_zero this

lemma analyticOrderAt_ge_one_of_zero (f : ℂ → ℂ) (z : ℂ) (hf : AnalyticAt ℂ f z) (hz : f z = 0) (hfinite : analyticOrderAt f z ≠ ⊤) : analyticOrderAt f z ≥ 1 := by
                                                                 
  have h_order_ne_zero : analyticOrderAt f z ≠ 0 := by
    intro h_order_zero
                                                              
    have h_f_ne_zero : f z ≠ 0 := by
      rw [← AnalyticAt.analyticOrderAt_eq_zero hf]
      exact h_order_zero
                                    
    exact h_f_ne_zero hz
                                                                      
  cases' h : analyticOrderAt f z with n
  ·                                 
                               
    rw [h] at hfinite
    exact False.elim (hfinite rfl)
  ·                                                 

    rw [h] at h_order_ne_zero
    have n_ne_zero : n ≠ 0 := by
      intro n_zero
      rw [n_zero, Nat.cast_zero] at h_order_ne_zero
      exact h_order_ne_zero rfl
                                 
    have n_ge_one : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr n_ne_zero
                            
    exact Nat.cast_le.mpr n_ge_one

lemma lem_m_rho_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (_h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≥ 1 := by
  intro ρ h_rho_in_KfR1
                                                     
  have h_f_rho_zero : f ρ = 0 := lem_frho_zero R R1 hR1_pos hR1_lt_R f h_f_analytic ρ h_rho_in_KfR1
                                                        
  have h_order_finite : analyticOrderAt f ρ ≠ ⊤ := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 ρ h_rho_in_KfR1
                       
  have h_f_analytic_at_rho : AnalyticAt ℂ f ρ := by
    apply h_f_analytic
                                            
    have h_R1_lt_1 : R1 < 1 := by linarith
    have h_rho_in_R1 : ρ ∈ Metric.closedBall 0 R1 := h_rho_in_KfR1.1
    exact Metric.closedBall_subset_closedBall (le_of_lt h_R1_lt_1) h_rho_in_R1
                                                                          
  exact analyticOrderAt_ge_one_of_zero f ρ h_f_analytic_at_rho h_f_rho_zero h_order_finite



lemma lem_denomAnalAt (S : Finset ℂ) (n : ℂ → ℕ)
    (_hn_pos : ∀ s ∈ S, 0 < n s) (w : ℂ) (hw : w ∉ S) :
    AnalyticAt ℂ (fun z => ∏ s ∈ S, (z - s) ^ (n s)) w ∧
    (∏ s ∈ S, (w - s) ^ (n s)) ≠ 0 := by
  constructor
  ·                          
                                 
    let f : ℂ → ℂ → ℂ := fun s z => (z - s) ^ (n s)
    have h_each_analytic : ∀ s ∈ S, AnalyticAt ℂ (f s) w := by
      intro s hs
      simp only [f]
                                                               
      have h_sub : AnalyticAt ℂ (fun z => z - s) w := by
        exact AnalyticAt.sub analyticAt_id analyticAt_const
                                              
      exact h_sub.pow (n s)
    have h_prod := Finset.analyticAt_prod S h_each_analytic
    convert (preTransparency := .instances) h_prod using 1
    first | rfl | (ext z; simp [f])
  ·                                
    apply Finset.prod_ne_zero_iff.mpr
    intro s hs
    apply pow_ne_zero
                     
    intro h_eq
                                         
    have h_w_eq_s : w = s := by
      rwa [← sub_eq_zero]
                                              
    rw [h_w_eq_s] at hw
    exact hw hs

lemma lem_ratioAnalAt (w : ℂ) (R R1 : ℝ) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (h : ℂ → ℂ) (hh : AnalyticAt ℂ h w)
    (S : Finset ℂ) (_hS : ↑S ⊆ Metric.closedBall (0 : ℂ) R1) (n : ℂ → ℕ)
    (hn_pos : ∀ s ∈ S, 0 < n s)
    (hw : w ∈ Metric.closedBall (0 : ℂ) 1 \ ↑S) :
    AnalyticAt ℂ (fun z => h z / ∏ s ∈ S, (z - s) ^ (n s)) w := by
  classical
                                                  
  have hden := lem_denomAnalAt (S := S) (n := n)
      (_hn_pos := hn_pos) (w := w)
      (hw := by simpa using hw.2)
                                                   
  exact AnalyticAt.div hh hden.1 hden.2


lemma lem_Cf_analytic_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    AnalyticAt ℂ (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) z := by

  have h_ratio_analytic : AnalyticAt ℂ (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat) z := by
    apply lem_ratioAnalAt z R R1 hR1_lt_R hR_lt_1 f

    · apply h_f_analytic
      exact Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1) hz.1

    · intro ρ hρ
      have h_mem : ρ ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hρ
      exact h_mem.1

    · intro s hs
      have h_s_in_zeros : s ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hs
      have h_order_ge_1 := lem_m_rho_ge_1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      have h_order_finite := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros

      cases' h_cases : analyticOrderAt f s with n
      ·                    
        rw [h_cases] at h_order_finite
        exact False.elim (h_order_finite rfl)
      ·                               
        have n_ge_1 : n ≥ 1 := by
          rw [h_cases] at h_order_ge_1
          exact Nat.cast_le.mp h_order_ge_1
        simp
        exact Nat.pos_iff_ne_zero.mpr (ne_of_gt n_ge_1)

    · constructor
      · exact Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1) hz.1
      ·                                     
        intro h_z_in_finset
        have h_z_in_zeros : z ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp h_z_in_finset
        exact hz.2 h_z_in_zeros

  have h_eventually_eq : (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat) =ᶠ[nhds z]
    (fun w => Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ w) := by
                                                           
    have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := hz.2
    have h_open : IsOpen (Set.compl (zerosetKfR R1 (by linarith) f)) := h_finite_zeros.isClosed.isOpen_compl
    apply Filter.eventually_of_mem (h_open.mem_nhds hz_not_in)
    intro w hw_not_in_compl
                                                              
    have hw_not_in_zeros : w ∉ zerosetKfR R1 (by linarith) f := hw_not_in_compl
                                                         
    show f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat =
         Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ w
                                                                          
    rw [Cf, dif_neg hw_not_in_zeros]

  exact h_ratio_analytic.congr h_eventually_eq

lemma lem_Cf_at_sigma_onK
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z = σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ z z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  refine Filter.Eventually.of_forall ?_
  intro z hz
  subst hz
  simp [Cf, hσ]


lemma lem_Cf_at_sigma_offK0
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z ≠ σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z /
      ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
                                        
  obtain ⟨h_σ_analytic, h_σ_ne_zero, h_f_eq⟩ := h_σ_spec σ hσ

  have h_σ_eventually_nonzero : ∀ᶠ z in nhds σ, h_σ σ z ≠ 0 := by
    have h_cont : ContinuousAt (h_σ σ) σ := h_σ_analytic.continuousAt
    exact h_cont.eventually_ne h_σ_ne_zero

  have h_f_eventually_nonzero : ∀ᶠ z in nhds σ, z ≠ σ → f z ≠ 0 := by
    filter_upwards [h_f_eq, h_σ_eventually_nonzero] with z h_fz_eq h_σz_nonzero
    intro hz_ne
    rw [h_fz_eq]
    apply mul_ne_zero
    · apply pow_ne_zero
      exact sub_ne_zero.mpr hz_ne
    · exact h_σz_nonzero

  have h_eventually_not_in_zeroset : ∀ᶠ z in nhds σ, z ≠ σ → z ∉ zerosetKfR R1 (by linarith) f := by
    filter_upwards [h_f_eventually_nonzero] with z h_fz_nonzero
    intro hz_ne hz_in_zeroset
    exact h_fz_nonzero hz_ne hz_in_zeroset.2

  filter_upwards [h_f_eq, h_eventually_not_in_zeroset] with z h_fz_eq h_not_in_zeroset
  intro hz_ne
                                                                    
  have hz_not_in_K : z ∉ zerosetKfR R1 (by linarith) f := h_not_in_zeroset hz_ne
                                                       
  unfold Cf
  simp [hz_not_in_K, h_fz_eq]

lemma lem_prod_no_sigma1
    {R R1 : ℝ} {hR1_pos : 0 < R1} {_hR1_lt_R : R1 < R} {_hR_lt_1 : R < 1}
    {f : ℂ → ℂ} {_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z} {_h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) (z : ℂ) :
    ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat =
    (z - σ) ^ (analyticOrderAt f σ).toNat *
    ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  classical
  have hmem : σ ∈ h_finite_zeros.toFinset :=
    (Set.Finite.mem_toFinset (hs := h_finite_zeros)).2 hσ
  simpa using
    (Finset.mul_prod_erase (s := h_finite_zeros.toFinset)
      (f := fun ρ => (z - ρ) ^ (analyticOrderAt f ρ).toNat) (a := σ) hmem).symm


lemma lem_Cf_at_sigma_offK
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z ≠ σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
                                            
  have h_cf_form := @lem_Cf_at_sigma_offK0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ

  filter_upwards [h_cf_form] with z h_cf_z
  intro hz_ne_sigma
                                              
  rw [h_cf_z hz_ne_sigma]
                                                 
  have h_prod_decomp := @lem_prod_no_sigma1 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros σ hσ z
                                                                            
  rw [h_prod_decomp]
                                                                  
  apply mul_div_mul_left
                       
  apply pow_ne_zero
  exact sub_ne_zero.mpr hz_ne_sigma

lemma lem_Cf_at_sigma
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ,
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
                                                 
  have h_on := @lem_Cf_at_sigma_onK R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ
  have h_off := @lem_Cf_at_sigma_offK R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ
                                      
  filter_upwards [h_on, h_off] with z hz_on hz_off
  by_cases h : z = σ
  ·                                                                
    have eq_result := hz_on h
                                                                  
    rw [h] at eq_result ⊢
    exact eq_result
  ·                                  
    exact hz_off h

lemma lem_h_ratio_anal
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (σ : ℂ) (_hσ : σ ∈ zerosetKfR R1 (by linarith) f)
    (g : ℂ → ℂ) (hg_analytic : AnalyticAt ℂ g σ) :
    AnalyticAt ℂ
      (fun z => g z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
        (z - ρ) ^ (analyticOrderAt f ρ).toNat) σ := by
                                                                             
  have hden := lem_denomAnalAt (S := h_finite_zeros.toFinset.erase σ)
    (n := fun ρ => (analyticOrderAt f ρ).toNat)
    (_hn_pos := by
      intro s hs
      have h_s_in_zeros : s ∈ zerosetKfR R1 (by linarith) f := by
        have h_mem_erase : s ∈ h_finite_zeros.toFinset.erase σ := hs
        have h_mem_orig : s ∈ h_finite_zeros.toFinset := Finset.mem_of_mem_erase h_mem_erase
        exact h_finite_zeros.mem_toFinset.mp h_mem_orig
      have h_order_ge_1 := lem_m_rho_ge_1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      have h_order_finite := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      cases' h_cases : analyticOrderAt f s with n
      ·                    
        rw [h_cases] at h_order_finite
        exact False.elim (h_order_finite rfl)
      ·                               
        have n_ge_1 : n ≥ 1 := by
          rw [h_cases] at h_order_ge_1
          exact Nat.cast_le.mp h_order_ge_1
        simp
        exact Nat.pos_iff_ne_zero.mpr (ne_of_gt n_ge_1))
    (w := σ)
    (hw := by
      simp [Finset.mem_erase])
                                                   
  exact AnalyticAt.div hg_analytic hden.1 hden.2

lemma lem_Cf_analytic_at_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    AnalyticAt ℂ (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) σ := by
                                                                               
  have h_eventually_eq := @lem_Cf_at_sigma R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ

  obtain ⟨h_σ_analytic, _, _⟩ := h_σ_spec σ hσ
  have h_ratio_analytic := @lem_h_ratio_anal R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros σ hσ (h_σ σ) h_σ_analytic

  have h_rev_eq : (fun z => h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat) =ᶠ[nhds σ]
                  (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) := by
    filter_upwards [h_eventually_eq] with z h_z
    exact h_z.symm

  exact AnalyticAt.congr h_ratio_analytic h_rev_eq


lemma lem_f_nonzero_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {_hR1_lt_R : R1 < R} {_hR_lt_1 : R < 1}
    {f : ℂ → ℂ} {_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z} {_h_f_nonzero_at_zero : f 0 ≠ 0}
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f) :
    f z ≠ 0 := by
  exact fun h => hz.2 ⟨hz.1, h⟩

lemma lem_Cf_nonzero_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z ≠ 0 := by
                                                     
  have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := hz.2

  have h_cf_eq : Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
    unfold Cf
    simp [hz_not_in]

  rw [h_cf_eq]

  apply div_ne_zero

  · apply @lem_f_nonzero_off_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero z hz

  · apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
                                                     
    apply pow_ne_zero
                                  
    intro h_eq
                                                            
    have hz_eq_rho : z = ρ := by
      rwa [sub_eq_zero] at h_eq
                                                                             
    have hρ_in : ρ ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hρ
    rw [hz_eq_rho] at hz_not_in
    exact hz_not_in hρ_in

lemma lem_Cf_nonzero_on_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ σ ≠ 0 := by
  have hnum : h_σ σ σ ≠ 0 := (h_σ_spec σ hσ).2.1
  have hden :
      (∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
        (σ - ρ) ^ (analyticOrderAt f ρ).toNat) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro ρ hρmem
    have hρ_ne_σ : ρ ≠ σ := (Finset.mem_erase.mp hρmem).1
    have hσ_ne_ρ : σ ≠ ρ := hρ_ne_σ.symm
    exact pow_ne_zero _ (sub_ne_zero.mpr hσ_ne_ρ)
  have :
      h_σ σ σ /
          ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
            (σ - ρ) ^ (analyticOrderAt f ρ).toNat ≠
        0 := by
    exact div_ne_zero hnum hden
  simpa [Cf, hσ] using this

lemma lem_Cf_never_zero
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z ≠ 0 := by
                                                         
  by_cases h : z ∈ zerosetKfR R1 (by linarith) f
  ·                                           
    exact lem_Cf_nonzero_on_K h_finite_zeros h_σ h_σ_spec z h
  ·                                           
    have hz_diff : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f := ⟨hz, h⟩
    exact lem_Cf_nonzero_off_K h_finite_zeros h_σ h_σ_spec z hz_diff












theorem lem_rho_in_disk_R1
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (_hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    norm ρ ≤ R1 := by
                                                                      
  have h_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R1 := h_rho_in_KfR1.1
                                                                     
  rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_ball
  simp only [sub_zero] at h_in_ball
  exact h_in_ball

theorem lem_zero_not_in_Kf (R R1 : ℝ)
  (hR1_pos : 0 < R1)
  (_hR1_lt_R : R1 < R)
  (f : ℂ → ℂ)
  (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z) :
    f 0 ≠ 0 → 0 ∉ zerosetKfR R1 (by linarith) f := by
  intro h_f_zero_ne_zero h_zero_in_KfR1
                                                  
  have h_f_zero_eq_zero : f 0 = 0 := h_zero_in_KfR1.2
                                                 
  exact h_f_zero_ne_zero h_f_zero_eq_zero

lemma lem_rho_ne_zero (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f, ρ ≠ 0 := by
  intro ρ h_ρ_in_zeros h_ρ_eq_zero
                                                         
  rw [h_ρ_eq_zero] at h_ρ_in_zeros
                                            
  have h_zero_not_in : 0 ∉ zerosetKfR R1 (by linarith) f :=
    lem_zero_not_in_Kf R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero
  exact h_zero_not_in h_ρ_in_zeros

lemma lem_mod_pos_iff_ne_zero (z : ℂ) : z ≠ 0 → norm z > 0 :=
  lem_abspos z

theorem lem_mod_rho_pos
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) :
    ∀ (ρ : ℂ), ρ ∈ zerosetKfR R1 (by linarith) f → norm ρ > 0 := by
  intro ρ h_ρ_in_zeros
                          
  have h_ρ_ne_zero : ρ ≠ 0 :=
    lem_rho_ne_zero R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros
                                                                 
  exact lem_mod_pos_iff_ne_zero ρ h_ρ_ne_zero


lemma lem_inv_mono_decr (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : 1 / x ≥ 1 / y := by
                                   
  have hy : 0 < y := lt_of_lt_of_le hx hxy
                                                       
  exact one_div_le_one_div_of_le hx hxy

lemma lem_inv_mod_rho_ge_inv_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    1 / norm ρ ≥ 1 / R1 := by
                                                    
  have h_abs_ρ_le_R1 : norm ρ ≤ R1 :=
    lem_rho_in_disk_R1 R R1 hR1_pos hR1_lt_R f ρ h_rho_in_KfR1
                                                            
  have h_abs_ρ_pos : norm ρ > 0 :=
    lem_mod_rho_pos R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1
                   
  have h_R1_pos : R1 > 0 := by
    linarith
                                                                   
  exact lem_inv_mono_decr (norm ρ) R1 h_abs_ρ_pos h_abs_ρ_le_R1


theorem lem_R_div_mod_rho_ge_R_div_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) (ρ : ℂ)
    (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    R / norm ρ ≥ R / R1 := by
                                             
  have h_inv_ineq : 1 / norm ρ ≥ 1 / R1 :=
    lem_inv_mod_rho_ge_inv_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1

  have h_R_div_abs_ρ_eq : R * (1 / norm ρ) = R / norm ρ := by ring
  have h_R_div_R1_eq : R * (1 / R1) = R / R1 := by ring
  rw [← h_R_div_abs_ρ_eq, ← h_R_div_R1_eq]
  exact mul_le_mul_of_nonneg_left h_inv_ineq (by linarith)

theorem lem_R_div_mod_rho_ge_R_over_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) (ρ : ℂ)
    (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    R / norm ρ ≥ (R/R1 : ℝ) := by
                                
  have h_ineq1 : R / norm ρ ≥ R / R1 :=
    lem_R_div_mod_rho_ge_R_div_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1
                           
  linarith

theorem lem_mod_of_prod2 {ι : Type*} (K : Finset ι) (w : ι → ℂ) :
    ‖∏ ρ ∈ K, w ρ‖ = ∏ ρ ∈ K, ‖w ρ‖ := by
  classical
  refine Finset.induction_on K ?h0 ?hstep
  · simp
  · intro a s ha ih
                                                       
    simp [Finset.prod_insert ha, ih]

lemma lem_mod_Bf_is_prod_mod (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ)
    (hz : z ∉ zerosetKfR R1 (by linarith) f) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat‖ := by
                                                                          
  unfold Bf
  rw [norm_mul]
                                                                                            
  rw [lem_mod_of_prod2]
                                                                                  
  have hCf : Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
    unfold Cf
    simp only [hz, ↓reduceDIte]
  rw [hCf, norm_div]
                                              
  rw [lem_mod_of_prod2]
                                                                        
  rw [div_mul_eq_mul_div]
                                                                                                    
  rw [mul_div_assoc]
                                                    
  rw [← Finset.prod_div_distrib]
  congr 2
  ext ρ
                                   
  rw [← norm_div, ← div_pow]
  congr 2
                                                  
  ring

lemma lem_abs_pow (w : ℂ) (n : ℕ) : ‖w ^ n‖ = ‖w‖ ^ n := by
  simp


lemma lem_mod_Bf_prod_mod (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
  (z : ℂ)
  (hz : z ∉ zerosetKfR R1 (by linarith) f) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ ^ (analyticOrderAt f ρ).toNat := by
                                                                                 
  have h1 := lem_mod_Bf_is_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz
  rw [h1]
                                                              
  congr 2
  ext ρ
  rw [lem_abs_pow]

lemma lem_mod_Bf_at_0 (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖((R : ℂ) / (-ρ))‖ ^ (analyticOrderAt f ρ).toNat := by
                                                                                       
  have hz0 : 0 ∉ zerosetKfR R1 (by linarith) f :=
    lem_zero_not_in_Kf R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero
  rw [lem_mod_Bf_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec 0 hz0]
                                                                                  
  congr 2
  ext ρ
  congr 1
  simp only [zero_mul, zero_div, sub_zero, zero_sub]

lemma lem_mod_div_ (w1 w2 : ℂ) (_hw2_ne_zero : w2 ≠ 0) : ‖w1 / w2‖ = ‖w1‖ / ‖w2‖ := by
  simp


lemma lem_mod_div_and_neg (R : ℝ) (hR_pos : 0 < R) (ρ : ℂ) (h_rho_ne_zero : ρ ≠ 0) :
  ‖(R : ℂ) / (-ρ)‖ = R / ‖ρ‖ := by
                                                              
  have hden : (-ρ) ≠ 0 := by simpa using neg_ne_zero.mpr h_rho_ne_zero
  have hdiv := lem_mod_div_ (R : ℂ) (-ρ) hden
  calc
    ‖(R : ℂ) / (-ρ)‖ = ‖(R : ℂ)‖ / ‖-ρ‖ := hdiv
    _ = ‖(R : ℂ)‖ / ‖ρ‖ := by simp [norm_neg]
    _ = |R| / ‖ρ‖ := by simp
    _ = R / ‖ρ‖ := by simp [abs_of_pos hR_pos]

theorem lem_mod_Bf_at_0_eval  (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
                               
  rw [lem_mod_Bf_at_0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec]
                                               
  congr 1
                                                         
  apply Finset.prod_congr rfl
  intro ρ hρ

  have h_ρ_ne_zero : ρ ≠ 0 := by
                                                             
    have h_ρ_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := by
      exact (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
    exact lem_rho_ne_zero R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros
                                                  
  rw [lem_mod_div_and_neg R (by linarith) ρ h_ρ_ne_zero]


theorem lem_mod_Bf_at_0_as_ratio  (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
  exact lem_mod_Bf_at_0_eval R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec

lemma lem_prod_ineq {ι : Type*} (K : Finset ι) (a b : ι → ℝ)
    (h_nonneg : ∀ ρ ∈ K, 0 ≤ a ρ) (h_le : ∀ ρ ∈ K, a ρ ≤ b ρ) :
    ∏ ρ ∈ K, a ρ ≤ ∏ ρ ∈ K, b ρ := by
  exact Finset.prod_le_prod h_nonneg h_le






lemma lem_mod_lower_bound_1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (_hR_lt_1 : R < 1) :
    ∏ ρ ∈ h_finite_zeros.toFinset,
      (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat ≥ 1 := by
  classical
  set K := h_finite_zeros.toFinset

  have h_base_ge_1 : (1 : ℝ) < (R/R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have h :=
    lem_prod_ineq K (fun _ : ℂ => (1 : ℝ))
      (fun ρ : ℂ => (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
      (by intro ρ hρ; norm_num)
      (by
        intro ρ hρ
        simpa using (one_le_pow₀ (by linarith [h_base_ge_1])))
  simpa [K] using h

theorem lem_mod_Bf_at_0_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≥ 1 := by
                                      
  have R_over_R1_nonneg : 1 < R / R1 := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have R_over_R1_nonneg : 0 ≤ R / R1 := by linarith
  have h_f_nonzero_at_zero : f 0 ≠ 0 := by
    rw [hf0_eq_one]; norm_num
                                                                    
  rw [lem_mod_Bf_at_0_as_ratio R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros]
                                     
  rw [hf0_eq_one, norm_one, one_mul]
                                                    
  have h_prod_ge : ∏ ρ ∈ h_finite_zeros.toFinset, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat ≥
                   ∏ ρ ∈ h_finite_zeros.toFinset, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat := by
    apply Finset.prod_le_prod
                       
    · intro ρ hρ
      apply pow_nonneg
      apply R_over_R1_nonneg
                                            
    · intro ρ hρ
      have h_ρ_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := by
        exact (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
                                                   
      have h_ratio_ge : R / ‖ρ‖ ≥ (R/R1 : ℝ) := by
                                                    
        have h_norm_abs_eq : ‖ρ‖ = norm ρ := by rfl
        rw [h_norm_abs_eq]
        exact lem_R_div_mod_rho_ge_R_over_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros

      have h_3_2_pos : (1 : ℝ) < (R/R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
      have h_3_2_pos : (0 : ℝ) < (R/R1 : ℝ) := by linarith
      have h_ratio_pos : (0 : ℝ) ≤ R / ‖ρ‖ := by
        linarith [h_ratio_ge]
      exact pow_le_pow_left₀ R_over_R1_nonneg h_ratio_ge (analyticOrderAt f ρ).toNat
                                                          
  have h_3_2_prod_ge_1 : ∏ ρ ∈ h_finite_zeros.toFinset, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat ≥ 1 :=
    lem_mod_lower_bound_1 R R1 hR1_pos hR1_lt_R f h_f_analytic hf0_eq_one h_finite_zeros hR_lt_1
                                                     
  exact le_trans h_3_2_prod_ge_1 h_prod_ge
  assumption



lemma lem_finset_prod_analyticAt {α : Type*} {S : Finset α} {g : α → ℂ → ℂ} (w : ℂ) :
  (∀ a ∈ S, AnalyticAt ℂ (g a) w) → AnalyticAt ℂ (fun z => ∏ a ∈ S, g a z) w := by
  intro h
  classical
  induction S using Finset.induction with
  | empty =>
                                                                
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | insert a s ha ih =>
                                                     
    simp only [Finset.prod_insert ha]
                                               
    apply AnalyticAt.fun_mul
    ·                        
      apply h
      exact Finset.mem_insert_self a s
    ·                                                           
      apply ih
      intro b hb
      apply h
      exact Finset.mem_insert_of_mem hb






theorem lem_Bf_is_analytic (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) (Metric.closedBall (0 : ℂ) R) := by
                                   
  intro z hz

  have h_blaschke_linear : ∀ ρ ∈ h_finite_zeros.toFinset,
    AnalyticAt ℂ (fun w => (R : ℂ) - star ρ * w / (R : ℂ)) z := by
    intro ρ hρ
                                         
    have h_eq : (fun w : ℂ => (R : ℂ) - star ρ * w / (R : ℂ)) =
                (fun w : ℂ => (R : ℂ) + (-(star ρ) / (R : ℂ)) * w) := by
      funext w
      field_simp
      ring
    rw [h_eq]
    exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)

  have h_powers : ∀ ρ ∈ h_finite_zeros.toFinset,
    AnalyticAt ℂ (fun w => ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) z := by
    intro ρ hρ
    exact (h_blaschke_linear ρ hρ).fun_pow _

  have h_product : AnalyticAt ℂ (fun w => ∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) z := by
                                                                       
    apply lem_finset_prod_analyticAt z
    intro ρ hρ
    apply h_powers
    exact hρ
                                                             
  by_cases hz_in : z ∈ zerosetKfR R1 (by linarith) f
  ·                                                                                 
    have h_cf_at_sigma := @lem_Cf_analytic_at_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_in
                                                                          
    exact AnalyticAt.fun_mul h_cf_at_sigma h_product

  ·                                                    
    have hz_in_compl : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f := by
      constructor
      · exact hz
      · exact hz_in
    have h_cf_off := @lem_Cf_analytic_off_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_in_compl
    exact AnalyticAt.fun_mul h_cf_off h_product

lemma complex_mul_star_eq_norm_sq (z : ℂ) : z * star z = (‖z‖ ^ 2 : ℂ) := by
                                                      
  rw [Complex.star_def]
                                                    
  exact Complex.mul_conj' z

lemma lem_mod_Bf_eq_mod_f_on_boundary (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ = ‖f z‖ := by
  intro z hz
                                                                              
  have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := by
    intro h_in
                                                    
    have h_norm_le_R1 : ‖z‖ ≤ R1 := by simpa [sub_zero] using (h_in.1 : z ∈ Metric.closedBall (0 : ℂ) R1)
                                                  
    have h_norm_eq_R : ‖z‖ = R := by simpa using hz
    linarith [h_norm_le_R1, h_norm_eq_R, hR1_lt_R]
  rw [lem_mod_Bf_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_not_in]

  have h_each_factor_one : ∀ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ = 1 := by
    intro ρ hρ

    have z_ne_rho : z ≠ ρ := by
      intro h_eq
      have rho_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
      have rho_bound : ‖ρ‖ ≤ R1 := by
        have h_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R1 := rho_in_zeros.1
        rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_ball
        simpa using h_in_ball
      have R1_lt_R : R1 < R := by linarith
      rw [← h_eq, hz] at rho_bound
      linarith [R1_lt_R]

    rw [Complex.norm_div]

    have z_conj_eq : z * star z = (R ^ 2 : ℂ) := by
      rw [complex_mul_star_eq_norm_sq z, hz, pow_two]

    have num_rewrite : (R : ℂ) - z * star ρ / (R : ℂ) = ((R : ℂ)^2 - z * star ρ) / (R : ℂ) := by
      have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast (hR1_pos.trans hR1_lt_R).ne'
      field_simp [hRne]

    rw [num_rewrite, Complex.norm_div]

    have factor_eq : (R : ℂ)^2 - z * star ρ = z * star (z - ρ) := by
      rw [← z_conj_eq, star_sub]
      ring

    rw [factor_eq, Complex.norm_mul, norm_star, ←hz]
    have hRpos : 0 < R := hR1_pos.trans hR1_lt_R
    have hnorm_denom : ‖z - ρ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr z_ne_rho)
    simp [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, hnorm_denom, hRpos.ne']

  have h_prod_one : ∏ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ ^ (analyticOrderAt f ρ).toNat = 1 := by
                                        
    rw [← Finset.prod_congr rfl (fun ρ hρ => by rw [h_each_factor_one ρ hρ, one_pow])]
    rw [Finset.prod_const_one]

  rw [h_prod_one, mul_one]

lemma lem_Bf_bounded_on_boundary (B R R1 : ℝ) (_hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
                                             
  intro z hz
  have hz_le : ‖z‖ ≤ R := le_of_eq hz
  have h_eq :=
    lem_mod_Bf_eq_mod_f_on_boundary R R1 (by linarith) hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz
  simpa [h_eq] using hf_le_B z hz_le


lemma mem_closedBall_of_norm_le {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) : z ∈ Metric.closedBall (0 : ℂ) R := by
  have : dist z (0 : ℂ) ≤ R := by simpa [Complex.dist_eq, sub_zero] using hz
  simpa [Metric.closedBall] using this

lemma closure_ball_eq_closedBall_center (R : ℝ) (hR : 0 < R) :
  closure (Metric.ball (0 : ℂ) R) = Metric.closedBall (0 : ℂ) R := by
  simpa using (closure_ball (x := (0 : ℂ)) (r := R) (ne_of_gt hR))

lemma lem_max_mod_principle_for_Bf (B R : ℝ) (hB : 1 < B) (hR_pos : 0 < R)
    (fB : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ fB (Metric.closedBall (0 : ℂ) R))
  (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R → ‖fB z‖ ≤ B) :
  ∀ z : ℂ, ‖z‖ ≤ R → ‖fB z‖ ≤ B := by
  intro z hz
                               
  have hB0 : 0 ≤ B := le_of_lt (lt_trans zero_lt_one hB)
                                                                 
  have h_an_on_closure : AnalyticOn ℂ fB (closure (ballDR R)) := by
    simpa [ballDR, closure_ball_eq_closedBall_center R hR_pos] using h_analytic.analyticOn
                                                                        
  have h_le :=
    lem_HardMMP R B hR_pos hB0 fB h_an_on_closure (by
      intro z hzR; exact h_bd_boundary z hzR)
                                                                                 
  have hz_cl : z ∈ closure (ballDR R) := by
    have hz_closed : z ∈ Metric.closedBall (0 : ℂ) R := mem_closedBall_of_norm_le hz
    simpa [ballDR, closure_ball_eq_closedBall_center R hR_pos] using hz_closed
  exact h_le z hz_cl

lemma lem_Bf_bounded_in_disk_from_boundary (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
  have hA := lem_Bf_is_analytic R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec
  exact lem_max_mod_principle_for_Bf B R hB (by linarith)
    (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) hA h_bd_boundary

lemma lem_Bf_bounded_in_disk_from_f (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
  intro z hz
  have h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B :=
    lem_Bf_bounded_on_boundary B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec hf_le_B
  exact (lem_Bf_bounded_in_disk_from_boundary B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec h_bd_boundary) z hz




lemma lem_log_mono_inc {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Real.log x ≤ Real.log y := by
  exact Real.log_le_log hx hxy













variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)
variable (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
variable (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)

lemma f_zero_ne_zero (h_f_zero : f 0 = 1) : f 0 ≠ 0 := by
  rw [h_f_zero]; simp

lemma Bf_is_analytic_on_disk
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) (Metric.closedBall (0 : ℂ) R) :=
    let hspec := h_σ_spec
    lem_Bf_is_analytic R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
      h_finite_zeros h_σ hspec

lemma lem_Bf_eq_prod_Cf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z, Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      (∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) *
      (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z) := by
  intro z
  rw [Bf]
  ring

lemma lem_num_prod_never_zero_all
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (_hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1,
      (∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) ≠ 0 := by
  intro z hz
  apply Finset.prod_ne_zero_iff.mpr
  intro ρ hρ
  apply pow_ne_zero

  have hρ_mem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    rwa [Set.Finite.mem_toFinset h_finite_zeros] at hρ
  have hρ_bound : ‖ρ‖ ≤ R1 := by
    rw [zerosetKfR] at hρ_mem; simp at hρ_mem; exact hρ_mem.1
  have hz_bound : ‖z‖ ≤ R1 := by
    rw [Metric.mem_closedBall, dist_zero_right] at hz; exact hz

  have hR_pos : (0 : ℝ) < R := lt_trans hR1_pos hR1_lt_R

  have key_positive : (0 : ℝ) < R - R1 * R1 / R := by
                                                  
    have h1 : R1 * R1 < R * R := by
      apply mul_self_lt_mul_self (le_of_lt hR1_pos) hR1_lt_R
    have h2 : R1 * R1 / R < R := by
      rw [div_lt_iff₀ hR_pos]
      exact h1
    linarith [h2]

  suffices h : (0 : ℝ) < ‖(R : ℂ) - star ρ * z / (R : ℂ)‖ by
    exact norm_pos_iff.mp h

  have triangle_ineq : ‖(R : ℂ) - star ρ * z / (R : ℂ)‖ ≥ ‖(R : ℂ)‖ - ‖star ρ * z / (R : ℂ)‖ :=
    norm_sub_norm_le _ _

  have R_norm_eq : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_of_nonneg (le_of_lt hR_pos)]

  have product_bound : ‖star ρ * z / (R : ℂ)‖ ≤ R1 * R1 / R := by
    rw [norm_div, norm_mul, norm_star, R_norm_eq]

    have mult_bound : ‖ρ‖ * ‖z‖ ≤ R1 * R1 := by
      exact mul_le_mul hρ_bound hz_bound (norm_nonneg _) (le_of_lt hR1_pos)
                                                                                
    have : ‖ρ‖ * ‖z‖ / R ≤ R1 * R1 / R := by
      exact div_le_div_of_nonneg_right mult_bound (le_of_lt hR_pos)
    exact this

  rw [R_norm_eq] at triangle_ineq
  linarith [triangle_ineq, product_bound, key_positive]

lemma Bf_never_zero
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1, Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z ≠ 0 := by
  intro z hz
                                                               
  rw [lem_Bf_eq_prod_Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec]
                                                                  
  apply mul_ne_zero
  ·                                                                                  
    exact lem_num_prod_never_zero_all R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec z hz
  ·                                                       
    exact lem_Cf_never_zero h_finite_zeros h_σ h_σ_spec z hz


noncomputable def Lf : ℂ → ℂ :=
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  Classical.choose (log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := B_f)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      have h_num_ne_zero : B_f z ≠ 0 :=
        Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
      assumption
    )
)

lemma Lf_is_analytic
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec)
                     (Metric.closedBall (0 : ℂ) r) := by
  unfold Lf
  exact (Classical.choose_spec (log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
    )
  )).1

lemma Lf_at_0_is_0
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec 0 = 0 := by
  unfold Lf
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  let log_exists := log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := B_f)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      have h_num_ne_zero : B_f z ≠ 0 :=
        Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
      assumption
    )
  exact (Classical.choose_spec log_exists).2.1

lemma lem_BCII {L : ℂ → ℂ} {r M r₁ : ℝ}
    (hr_pos : 0 < r)
    (hM_pos : 0 < M)
    (hr₁_pos : 0 < r₁)
    (hr₁_lt_r : r₁  < r)
    (hL_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧ DifferentiableOn ℂ L U)
    (hL0 : L 0 = 0)
    (hre_L_le_M : ∀ w ∈ Metric.closedBall 0 r, (L w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r₁) :
norm (deriv L z) ≤ (16 * M * r ^ 2) / ((r - r₁) ^ 3) := by
  apply borel_caratheodory_II hr_pos hM_pos hr₁_pos hr₁_lt_r hL_domain hL0 hre_L_le_M hz

lemma re_Lf_as_diff_of_log_mods
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      Complex.re (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z) =
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) -
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)) := by
  intro z hz
                                                                                                                      
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  have h_Bf_analytic : AnalyticOnNhd ℂ B_f (Metric.closedBall (0 : ℂ) R) :=
    Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  have h_Bf_ne_zero : ∀ w ∈ Metric.closedBall (0 : ℂ) R1, B_f w ≠ 0 := by
    intro w hw
    exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec w hw

  have h_log_exists := log_of_analytic hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 h_Bf_analytic h_Bf_ne_zero
  have h_choose_spec := Classical.choose_spec h_log_exists

  have h_Lf_def : Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec = Classical.choose h_log_exists := by
    unfold Lf
    simp only [B_f]

  rw [h_Lf_def]
  exact (h_choose_spec.2.2.2 z hz).symm

lemma log_Bf_le_log_B
    (B R R1 : ℝ)
    (_hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_Bf_pos : ∀ z, norm z ≤ R1 →
                0 < norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z))
    (h_Bf_bound : ∀ z, norm z ≤ R1 →
                  norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z) ≤ B) :
    ∀ z, norm z ≤ R1 →
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) ≤ Real.log B := by
  intro z hz
  apply Real.log_le_log
  · exact h_Bf_pos z hz
  · exact h_Bf_bound z hz

lemma log_Bf_le_log_B2
    (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_Bf_bound : ∀ z, ‖z‖ ≤ R →
                  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z‖ ≤ B) :
    ∀ z, ‖z‖ ≤ R1 →
      Real.log (‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z‖) ≤ Real.log B := by
                                 
  apply log_Bf_le_log_B B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  ·                                                  
    intro z hz
    have hz_mem : z ∈ Metric.closedBall (0 : ℂ) R1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hz
    have hBf_ne_zero := Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz_mem
    exact norm_pos_iff.mpr hBf_ne_zero
  ·                                                    
    intro z hz
    have hz_le_R : ‖z‖ ≤ R := by linarith [hz, hR1_lt_R]
    exact h_Bf_bound z hz_le_R

lemma log_Bf_le_log_B3
    (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ R1 →
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) ≤ Real.log B := by
                                                                              
  apply log_Bf_le_log_B2 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
                                                       
  apply lem_Bf_bounded_in_disk_from_f B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec
                                                               
  exact h_f_bound

lemma log_Bf0_ge_0
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    0 ≤ Real.log (‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0‖) := by
                                                          
  have h_pos : 0 < (1 : ℝ) := by norm_num
  have h_Bf_ge_1 : 1 ≤ ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0‖ :=
    lem_mod_Bf_at_0_ge_1 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_f_zero h_finite_zeros h_σ h_σ_spec
  have h_log_mono := lem_log_mono_inc h_pos h_Bf_ge_1
  rw [Real.log_one] at h_log_mono
  exact h_log_mono

lemma re_Lf_le_log_B
    (B r R R1 : ℝ)
    (hB : 1 < B)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ r →
      Complex.re (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z) ≤ Real.log B := by
  intro z hz
                                                                                         
  rw [re_Lf_as_diff_of_log_mods r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z]
  ·                                           
                                                                 
    have hz_apply_BC_to_Lfle_R1 : ‖z‖ ≤ R1 := by linarith [hz, hr_lt_R1]
    have h1 := log_Bf_le_log_B3 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec h_f_bound z hz_apply_BC_to_Lfle_R1
    have h2 := log_Bf0_ge_0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
    linarith
  ·                                            
    exact Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hz)



lemma apply_BC_to_Lf
    (B r1 r R R1 : ℝ)
    (hB : 1 < B)
    (hr1_pos : 0 < r1)
    (hr1_lt_r : r1 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ r1 →
      norm (deriv (Lf (lt_trans hr1_pos hr1_lt_r : 0 < r) hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z) ≤
      (16 * Real.log B * r^2) / (r - r1)^3 := by
  classical
  intro z hz
                                        
  have hr_pos : 0 < r := lt_trans hr1_pos hr1_lt_r
                                                              
  let L := Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec
                                                                   
  have h_analytic_nhd :=
    Lf_is_analytic r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
                                                                             
  let U : Set ℂ :=
    { y | ∃ x ∈ Metric.closedBall (0 : ℂ) r, ∃ s : ℝ, 0 < s ∧ y ∈ Metric.ball x s ∧
        AnalyticOnNhd ℂ L (Metric.ball x s) }
  have hU_open : IsOpen U := by
    refine isOpen_iff_mem_nhds.mpr ?_
    intro y hy
    rcases hy with ⟨x, hxCB, s, hs_pos, hyin, hAnaBall⟩
    have hnhds : Metric.ball x s ∈ nhds y := (Metric.isOpen_ball.mem_nhds hyin)
    exact Filter.mem_of_superset hnhds (by intro z hz; exact ⟨x, hxCB, s, hs_pos, hz, hAnaBall⟩)
  have hCB_subset : Metric.closedBall (0 : ℂ) r ⊆ U := by
    intro x hx
    have hAt : AnalyticAt ℂ L x := h_analytic_nhd x hx
    rcases AnalyticAt.exists_ball_analyticOnNhd hAt with ⟨s, hs_pos, hAnaBall⟩
    have hx_in_ball : x ∈ Metric.ball x s := by
      simpa [Metric.mem_ball, dist_self] using hs_pos
    exact ⟨x, hx, s, hs_pos, hx_in_ball, hAnaBall⟩
  have hDiffU : DifferentiableOn ℂ L U := by
    intro y hy
    rcases hy with ⟨x, hxCB, s, hs_pos, hy_in, hAnaBall⟩
                                                          
    have hAt : AnalyticAt ℂ L y := hAnaBall y hy_in
    exact (AnalyticAt.differentiableAt hAt).differentiableWithinAt
                        
  have hL_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧ DifferentiableOn ℂ L U :=
    ⟨U, hU_open, hCB_subset, hDiffU⟩
             
  have hL0 : L 0 = 0 := by
    simpa [L] using (Lf_at_0_is_0 r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
                                                
  have hre_L_le_M : ∀ w ∈ Metric.closedBall 0 r, (L w).re ≤ Real.log B := by
    intro w hw
    have hw' : norm w ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    exact re_Lf_le_log_B B r R R1 hB hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec h_f_bound w hw'
                        
  have hz' : z ∈ Metric.closedBall 0 r1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
                                
  have hBC :=
    lem_BCII hr_pos (Real.log_pos hB) hr1_pos hr1_lt_r hL_domain hL0 hre_L_le_M hz'
             
  simpa [L] using hBC




lemma logDerivconst {a : ℂ} {g : ℂ → ℂ} (ha : a ≠ 0) :
    ∀ z, logDeriv (fun w ↦ a * g w) z = logDeriv g z := by
  intro z
  exact logDeriv_const_mul z a ha


lemma Lf_deriv_is_logBf_deriv (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
      logDeriv (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w /
                           Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0) z =
      logDeriv (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w) z := by
  intro z _
                                                      
  have h_eq : (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w /
                       Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0) =
              (fun w ↦ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)⁻¹ *
                       Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w) := by
    ext w
    rw [div_eq_mul_inv]
    ring
  rw [h_eq]
                                               
  have h0_in_ball : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R1 := by
    simp [Metric.mem_closedBall]
    exact le_of_lt hR1_pos
  have h_Bf0_ne_zero := Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec 0 h0_in_ball
                                      
  have h_inv_ne_zero : (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)⁻¹ ≠ 0 :=
    inv_ne_zero h_Bf0_ne_zero
                        
  exact logDerivconst h_inv_ne_zero z


lemma deriv_over_fun_is_logDeriv {g : ℂ → ℂ} : ∀ z, deriv g z / g z = logDeriv g z := by
  intro z
  rfl

lemma logDerivmul {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hf_ne : f z ≠ 0) (hg_ne : g z ≠ 0) :
    logDeriv (fun w ↦ f w * g w) z = logDeriv f z + logDeriv g z := by
  exact logDeriv_mul z hf_ne hg_ne hf hg

lemma logDerivprod {K : Finset ℂ} {g : ℂ → ℂ → ℂ} {z : ℂ}
    (hg_diff : ∀ ρ ∈ K, DifferentiableAt ℂ (g ρ) z)
    (hg_ne : ∀ ρ ∈ K, g ρ z ≠ 0) :
    logDeriv (fun w ↦ ∏ ρ ∈ K, g ρ w) z = ∑ ρ ∈ K, logDeriv (g ρ) z := by
  simpa only [Finset.prod_fn] using logDeriv_prod hg_ne hg_diff

lemma logDerivdiv {h g : ℂ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℂ h z) (hg : DifferentiableAt ℂ g z)
    (hh_ne : h z ≠ 0) (hg_ne : g z ≠ 0) :
    logDeriv (fun w ↦ h w / g w) z = logDeriv h z - logDeriv g z := by
  exact logDeriv_div z hh_ne hg_ne hh hg

lemma logDerivfunpow {g : ℂ → ℂ} {z : ℂ} {m : ℕ}
    (hg : DifferentiableAt ℂ g z) :
    logDeriv (fun w ↦ (g w) ^ m) z = m * logDeriv g z := by
  exact logDeriv_fun_pow hg m

lemma z_minus_rho_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (_h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    z - ρ ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ w - ρ) z := by
  intro ρ hρ z hz
  have hz_pair := (Set.mem_sdiff z).1 hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R1 := hz_pair.1
  have hz_notK : z ∉ zerosetKfR R1 (by linarith) f := hz_pair.2
                               
  have hz_ne_rho : z ≠ ρ := by
    intro h_eq
    exact hz_notK (by simpa [h_eq] using hρ)
  have h_nonzero : z - ρ ≠ 0 := sub_ne_zero.mpr hz_ne_rho
                                        
  have hdiff : DifferentiableAt ℂ (fun w => w) z := differentiableAt_fun_id
  have hdiff_sub : DifferentiableAt ℂ (fun w => w - ρ) z := hdiff.sub_const ρ
  exact ⟨h_nonzero, hdiff_sub⟩

lemma blaschke_num_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (_h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R,
    R - (star ρ) * z / R ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ R - (star ρ) * w / R) z := by
  intro ρ hρ z hz
  constructor
  · intro hzero
    have hRne : (R : ℂ) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt (hR1_pos.trans hR1_lt_R)))
                                                                          
    have heq : (R : ℂ) = (star ρ) * z / (R : ℂ) := sub_eq_zero.mp hzero
    have hmul := congrArg (fun t : ℂ => t * (R : ℂ)) heq
    have heq_mul : (R : ℂ) * (R : ℂ) = (star ρ) * z := by
                                     
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hRne] using hmul
                              
    have hnorm_eq : ‖(R : ℂ)‖ * ‖(R : ℂ)‖ = ‖ρ‖ * ‖z‖ := by
      simpa [Complex.norm_mul, Complex.norm_conj] using congrArg (fun t : ℂ => ‖t‖) heq_mul
                                   
    have hz_norm_le : ‖z‖ ≤ R := by
      have hz' : dist z (0 : ℂ) ≤ R := (Metric.mem_closedBall.mp hz)
      simpa [dist_eq_norm] using hz'
    have hrho_norm_le : ‖ρ‖ ≤ R1 := by
      rcases hρ with ⟨hρ_ball, _hρ_zero⟩
      have : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_ball)
      simpa [dist_eq_norm] using this
    have hz_nonneg : 0 ≤ ‖z‖ := by simp
    have hR1_nonneg : 0 ≤ R1 := le_of_lt hR1_pos
    have hle : ‖ρ‖ * ‖z‖ ≤ R1 * R := by
      have h1 : ‖ρ‖ * ‖z‖ ≤ R1 * ‖z‖ := mul_le_mul_of_nonneg_right hrho_norm_le hz_nonneg
      have h2 : R1 * ‖z‖ ≤ R1 * R := mul_le_mul_of_nonneg_left hz_norm_le hR1_nonneg
      exact le_trans h1 h2
                                            
    have hnorm_R : ‖(R : ℂ)‖ = R := by
      have h1 : ‖(R : ℂ)‖ = |R| := by simp
      simp [abs_of_pos (hR1_pos.trans hR1_lt_R)]
                                         
    have : R * R = ‖ρ‖ * ‖z‖ := by simpa [hnorm_R] using hnorm_eq
    have hle' : R * R ≤ R1 * R := by simpa [this] using hle
                                                                     
    have hposR : 0 < R := hR1_pos.trans hR1_lt_R
    have hposRR : 0 < R * R := by nlinarith [hposR]
    have hlt : R1 * R < R * R := by
      exact mul_lt_mul_of_pos_right hR1_lt_R hposR
    exact (lt_irrefl _ (lt_of_le_of_lt hle' hlt))
  ·                                      
    have h_const : DifferentiableAt ℂ (fun _ : ℂ => (R : ℂ)) z := by
      simp
    have h_id : DifferentiableAt ℂ (fun w : ℂ => w) z := by
      simp
    have h_mul : DifferentiableAt ℂ (fun w : ℂ => (star ρ) * w) z := by
      simpa using h_id.const_mul (star ρ)
    have h_div : DifferentiableAt ℂ (fun w : ℂ => (star ρ) * w / (R : ℂ)) z := by
      simpa [div_eq_mul_inv] using h_mul.mul_const ((R : ℂ)⁻¹)
    simpa using h_const.sub h_div

lemma blaschke_frac_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    (R - (star ρ) * z / R) / (z - ρ) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro ρ hρ z hz
                                                 
  have hden := z_minus_rho_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ z hz
  have hden_ne : z - ρ ≠ 0 := hden.1
  have hden_diff : DifferentiableAt ℂ (fun w ↦ w - ρ) z := hden.2
                                                  
  have hz_in_small : z ∈ Metric.closedBall (0 : ℂ) R1 ∧
      z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_small : z ∈ Metric.closedBall (0 : ℂ) R1 := hz_in_small.1
                                                       
  have hz_dist_le_small : dist z (0 : ℂ) ≤ R1 := by
    simpa [Metric.mem_closedBall] using hz_small
  have hRle : R ≤ 1 := le_of_lt hR_lt_1
  have hR1_le_R : R1 ≤ R := le_of_lt hR1_lt_R
  have hR1_le_1 : R1 ≤ 1 := le_trans hR1_le_R hRle
  have hz_ball1 : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have hz_le1 : dist z (0 : ℂ) ≤ 1 := le_trans hz_dist_le_small hR1_le_1
    simpa [Metric.mem_closedBall] using hz_le1
                                               
  have hz_ballR : z ∈ Metric.closedBall (0 : ℂ) R := by
    have hz_le_R : dist z (0 : ℂ) ≤ R := le_trans hz_dist_le_small (le_of_lt hR1_lt_R)
    simpa [Metric.mem_closedBall] using hz_le_R
  have hnum := blaschke_num_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ z hz_ballR
  have hnum_ne : R - (star ρ) * z / R ≠ 0 := hnum.1
  have hnum_diff : DifferentiableAt ℂ (fun w ↦ R - (star ρ) * w / R) z := hnum.2
             
  refine And.intro ?_ ?_
  · intro h
    have h' : (R - (star ρ) * z / R) * (z - ρ)⁻¹ = 0 := by
      simpa [div_eq_mul_inv] using h
    rcases mul_eq_zero.mp h' with hnum0 | hinv0
    · exact hnum_ne hnum0
    · exact hden_ne (inv_eq_zero.mp hinv0)
  · exact hnum_diff.div hden_diff hden_ne

lemma blaschke_pow_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro ρ hρ z hz
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ z hz
  rcases hfrac with ⟨hne, hdiff⟩
  constructor
  · exact pow_ne_zero _ hne
  · convert (preTransparency := .instances) hdiff.pow ((analyticOrderAt f ρ).toNat) using 1

lemma blaschke_prod_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    (∏ ρ ∈ h_finite_zeros.toFinset, ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                        ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  classical
  constructor
  ·                                
    have hne_each : ∀ ρ ∈ h_finite_zeros.toFinset,
        ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 := by
      intro ρ hρ
      have hρ' : ρ ∈ zerosetKfR R1 (by linarith) f :=
        (h_finite_zeros.mem_toFinset).1 hρ
      have hpair :=
        blaschke_pow_diff_nonzero (R := R) (R1 := R1) (f := f)
          hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ' z hz
      exact hpair.1
    exact (Finset.prod_ne_zero_iff).2 hne_each
  ·                                    
    have hdiff_each : ∀ ρ ∈ h_finite_zeros.toFinset,
        DifferentiableAt ℂ
          (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
      intro ρ hρ
      have hρ' : ρ ∈ zerosetKfR R1 (by linarith) f :=
        (h_finite_zeros.mem_toFinset).1 hρ
      have hpair :=
        blaschke_pow_diff_nonzero (R := R) (R1 := R1) (f := f)
          hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ' z hz
      exact hpair.2
                                                                 
    have hdiff :=
      (DifferentiableAt.finsetProd (u := h_finite_zeros.toFinset)
        (f := fun ρ => fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
        (x := z) hdiff_each)
    have hfun_eq :
        (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
        =
        (∏ ρ ∈ h_finite_zeros.toFinset,
            (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)) := by
      funext w
      simp [Finset.prod_apply]
    exact hfun_eq.symm ▸ hdiff

lemma f_diff_nonzero_outside_Kf {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (_h_finite_zeros : (zerosetKfR R1 (by linarith ) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    f z ≠ 0 ∧ DifferentiableAt ℂ f z := by
  intro z hz
                                            
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R1 ∧
      z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_in_R1 : z ∈ Metric.closedBall (0 : ℂ) R1 := hz'.1
  have hz_notin : z ∉ zerosetKfR R1 (by linarith) f := hz'.2
                 
  have hz_nonzero : f z ≠ 0 := by
    intro hfz
    exact hz_notin ⟨hz_in_R1, hfz⟩
                                                               
  have hR1_lt_1 : R1 < 1 := by linarith
  have hsubset1 :
      Metric.closedBall (0 : ℂ) R1 ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.closedBall_subset_ball hR1_lt_1
  have hz_in_ball1 : z ∈ Metric.ball (0 : ℂ) 1 := hsubset1 hz_in_R1
  have hz_in_1 : z ∈ Metric.closedBall (0 : ℂ) 1 :=
    Metric.ball_subset_closedBall hz_in_ball1
  have hAna : AnalyticAt ℂ f z := h_f_analytic z hz_in_1
  have hDiff : DifferentiableAt ℂ f z := hAna.differentiableAt
  exact ⟨hz_nonzero, hDiff⟩


lemma logDeriv_fprod_is_sum {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ f w * ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    logDeriv f z + logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  have hf' := f_diff_nonzero_outside_Kf (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  rcases hf' with ⟨hf_ne, hf_diff⟩
  have hg' := blaschke_prod_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  rcases hg' with ⟨hg_ne, hg_diff⟩
  simpa using
    (logDerivmul (f:=f) (g:=fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
        ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) (z:=z)
      hf_diff hg_diff hf_ne hg_ne)








lemma div_mul_eq_mul_mul_inv_fun {α} (f A B : α → ℂ) :
  (fun w => (f w / A w) * B w) = (fun w => f w * (B w * (A w)⁻¹)) := by
  funext w
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]


lemma prod_num_mul_inv_den_eq_prod_ratio_fun_mem
  (K : Finset ℂ) (N D : ℂ → ℂ → ℂ) (m : ℂ → ℕ) :
  (fun w ↦ (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹)
  = (fun w ↦ ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ))) := by
  funext w
  classical
  calc
    (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹
        = (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) / (∏ ρ ∈ K, (D ρ w) ^ (m ρ)) := by
          simp [div_eq_mul_inv]
    _ = ∏ ρ ∈ K, ((N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ)) := by
          simp
    _ = ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ)) := by
          refine Finset.prod_congr rfl ?_
          intro ρ hρ
          have hpow_div :
              (N ρ w / D ρ w) ^ (m ρ)
                = (N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ) := by
            calc
              (N ρ w / D ρ w) ^ (m ρ)
                  = (N ρ w * (D ρ w)⁻¹) ^ (m ρ) := by
                        simp [div_eq_mul_inv]
              _ = (N ρ w) ^ (m ρ) * ((D ρ w)⁻¹) ^ (m ρ) := by
                        simpa using (mul_pow (N ρ w) ((D ρ w)⁻¹) (m ρ))
              _ = (N ρ w) ^ (m ρ) * ((D ρ w) ^ (m ρ))⁻¹ := by
                        simp
              _ = (N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ) := by
                        simp [div_eq_mul_inv]
          simpa using hpow_div.symm


lemma logDeriv_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
  (hfg : f =ᶠ[nhds z] g) : logDeriv f z = logDeriv g z := by
                                                                                         
  have hval : f z = g z := Filter.EventuallyEq.eq_of_nhds hfg
  have hderiv_eq_ev : deriv f =ᶠ[nhds z] deriv g := hfg.deriv
  have hderiv : deriv f z = deriv g z := Filter.EventuallyEq.eq_of_nhds hderiv_eq_ev
                                                      
  have hf := deriv_over_fun_is_logDeriv (g := f) z
  have hg := deriv_over_fun_is_logDeriv (g := g) z
  simp [hf.symm, hg.symm, hval, hderiv]

lemma logDeriv_Bf_is_sum :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \
          zerosetKfR R1 (by linarith) f,
    logDeriv (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) z =
    logDeriv f z +
      logDeriv
        (fun w ↦
          ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  classical
  intro z hz
                  
  set K : Finset ℂ := h_finite_zeros.toFinset
                                                                    
  let A : ℂ → ℂ := fun w => ∏ ρ ∈ K, (w - ρ) ^ (analyticOrderAt f ρ).toNat
  let BN : ℂ → ℂ := fun w => ∏ ρ ∈ K, (R - (star ρ) * w / R) ^ (analyticOrderAt f ρ).toNat
  let RatProd : ℂ → ℂ :=
    fun w => ∏ ρ ∈ K, ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat
                                                                              
  set S : Set ℂ := zerosetKfR R1 (by linarith) f
  have hS_fin : S.Finite := h_finite_zeros
  have hU_open : IsOpen Sᶜ := hS_fin.isClosed.isOpen_compl
  have hz_notin : z ∉ S := by
    rcases hz with ⟨_, hnotin⟩; exact hnotin
  have hzU : z ∈ Sᶜ := by simpa [Set.mem_compl] using hz_notin
  have hU_mem : Sᶜ ∈ nhds z := hU_open.mem_nhds hzU
  have h_ev :
      (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w)
        =ᶠ[nhds z]
      (fun w ↦ f w * RatProd w) := by
    refine Filter.eventually_of_mem hU_mem ?_
    intro w hwU
    have hw_notin : w ∉ S := by simpa [Set.mem_compl] using hwU
                                                         
    have hBf_w :
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w * BN w := by
      simp [Bf, BN, K]
    have hCf_w :
        Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = f w / A w := by
      simp [Cf, S, A, K, hw_notin]
                                                           
    have h_eq1 := div_mul_eq_mul_mul_inv_fun (f := f) (A := A) (B := BN)
    have h_eq1_w : (f w / A w) * BN w = f w * (BN w * (A w)⁻¹) := by
      simpa using congrArg (fun g : (ℂ → ℂ) => g w) h_eq1
    have h_eq2 :=
      prod_num_mul_inv_den_eq_prod_ratio_fun_mem
        (K := K)
        (N := fun ρ w ↦ (R - (star ρ) * w / R))
        (D := fun ρ w ↦ (w - ρ))
        (m := fun ρ ↦ (analyticOrderAt f ρ).toNat)
    have h_eq2_w : BN w * (A w)⁻¹ = RatProd w := by
      simpa [BN, A, RatProd] using congrArg (fun g : (ℂ → ℂ) => g w) h_eq2
                           
    calc
      Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = (f w / A w) * BN w := by simpa [hCf_w] using hBf_w
      _ = f w * (BN w * (A w)⁻¹) := h_eq1_w
      _ = f w * RatProd w := by simp [h_eq2_w]
                                       
  have hlog_congr := logDeriv_congr_of_eventuallyEq (f := fun w ↦
      Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w)
      (g := fun w ↦ f w * RatProd w) (z := z) h_ev
                                  
  have hsum :=
    (logDeriv_fprod_is_sum (R:=R) (R1:=R1) (f:=f)
      hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz)
  simpa [RatProd, K] using hlog_congr.trans hsum

lemma logDeriv_def_as_frac {f : ℂ → ℂ} {z : ℂ}
    (_hf : DifferentiableAt ℂ f z) (_hf_ne : f z ≠ 0) :
    logDeriv f z = deriv f z / f z := by
  simp [logDeriv]

theorem ball_containment {r R1 : ℝ} (_hr_pos : 0 < r) (hr_lt_R1 : r < R1) (z : ℂ) (hz : z ∈ Metric.closedBall 0 r) : z ∈ Metric.closedBall 0 R1 := by
  simp at *
  exact le_trans hz (le_of_lt hr_lt_R1)

theorem in_r_minus_kf {R1 r : ℝ} {f : ℂ → ℂ}
  (hr_pos : 0 < r)
  (hr_lt_R1 : r < R1)
  (z : ℂ)
  (hz : z ∈ Metric.closedBall 0 r \ zerosetKfR R1 (by linarith) f) :
   z ∈ Metric.closedBall 0 R1 \ zerosetKfR R1 (by linarith) f := by
  obtain ⟨h1, h2⟩ := hz
  have : z ∈ Metric.closedBall 0 R1 := by
    apply ball_containment hr_pos hr_lt_R1 z h1
  constructor <;> assumption

lemma Lf_deriv_step1 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                                ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
                                  
  have hz' : z ∈ Metric.closedBall (0 : ℂ) r ∧ z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) r := hz'.1
                               
  have hLf :=
    
    (Lf_deriv_is_logBf_deriv hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec
      z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)).symm
                                   
  have hsum :
      logDeriv (fun w ↦
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
          h_finite_zeros h_σ w) z =
      logDeriv f z +
        logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
    have h :=
      (logDeriv_Bf_is_sum (R := R) (R1 := R1) (r := r) (f := f) (h_σ := h_σ)
        hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros) z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
    simpa using h
                                                                              
  obtain ⟨hf_ne, hfdiff⟩ :=
    f_diff_nonzero_outside_Kf (R := R) (R1 := R1) (f := f)
      hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
  have hfrac : logDeriv f z = deriv f z / f z :=
    logDeriv_def_as_frac (f := f) (z := z) hfdiff hf_ne

  have hLf_eq_logDerivBf :
      deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
      logDeriv (fun w ↦
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
          h_finite_zeros h_σ w) z := by

    have hz_in_r : z ∈ Metric.closedBall (0 : ℂ) r := hz_ball
                                                               
    let B_f : ℂ → ℂ :=
      fun w => Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
    let log_exists := log_of_analytic
      (r1 := r) (R' := R1) (R := R)
      hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
      (B := B_f)
      (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1
                f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
      (hB_ne_zero := by
        intro w hw
        exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1
          f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec w hw)
    have hderiv_all : ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        deriv (Classical.choose log_exists) w = deriv B_f w / B_f w :=
      (Classical.choose_spec log_exists).2.2.1
    have hderiv_Lf :
        deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos
                    h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z
          = deriv B_f z / B_f z := by
                                                                            
      unfold Lf
                                                                                                       
      simpa using hderiv_all z hz_in_r
                                                  
    have h_as_log : deriv B_f z / B_f z = logDeriv B_f z :=
      deriv_over_fun_is_logDeriv (g := B_f) z
               
    simpa [B_f] using hderiv_Lf.trans h_as_log

  calc
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z
        = logDeriv (fun w ↦
            Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
              h_finite_zeros h_σ w) z := hLf_eq_logDerivBf
    _ = logDeriv f z +
          logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := hsum
    _ = deriv f z / f z +
          logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
            simp [hfrac]

lemma logDeriv_prod_is_sum {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    ∑ ρ ∈ h_finite_zeros.toFinset, logDeriv (fun w ↦
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  have hdiff : ∀ ρ ∈ h_finite_zeros.toFinset,
      DifferentiableAt ℂ (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
    intro ρ hρ
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f :=
      (h_finite_zeros.mem_toFinset).mp hρ
    have h := blaschke_pow_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρmem z hz
    exact h.2
  have hne : ∀ ρ ∈ h_finite_zeros.toFinset,
      ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 := by
    intro ρ hρ
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f :=
      (h_finite_zeros.mem_toFinset).mp hρ
    have h := blaschke_pow_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρmem z hz
    exact h.1
  simpa using
    (logDerivprod (K := h_finite_zeros.toFinset)
      (g := fun ρ w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
      (z := z) hdiff hne)

lemma logDeriv_power_is_mul {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ∀ ρ ∈ h_finite_zeros.toFinset,
    logDeriv (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    (analyticOrderAt f ρ).toNat * logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz ρ hρFin
  have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    simpa using (h_finite_zeros.mem_toFinset.mp hρFin)
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρmem z hz
  rcases hfrac with ⟨_hneq, hdiff⟩
  simpa using
    (logDerivfunpow (g := fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) (z := z)
      (m := (analyticOrderAt f ρ).toNat) hdiff)

lemma logDeriv_prod_is_sum_mul {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                    logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz
  classical
  have hsum :=
    logDeriv_prod_is_sum (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  refine hsum.trans ?_
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  exact
    logDeriv_power_is_mul (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz ρ hρ

lemma Lf_deriv_step2 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                                       logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz
  classical
  have h1 :=
    Lf_deriv_step1 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz
  have hsum :=
    logDeriv_prod_is_sum_mul (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
  have h2 := congrArg (fun t => deriv f z / f z + t) hsum
  exact h1.trans h2

lemma logDeriv_Blaschke_is_diff {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ∀ ρ ∈ h_finite_zeros.toFinset,
    logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z =
    logDeriv (fun w ↦ R - (star ρ) * w / R) z - logDeriv (fun w ↦ w - ρ) z := by
  intro z hz ρ hρ
  have hρ_set : ρ ∈ zerosetKfR R1 (by linarith) f := by
    exact (Set.Finite.mem_toFinset (hs := h_finite_zeros) (a := ρ)).mp hρ
  rcases hz with ⟨hz_in, hz_notin⟩
  have hden := z_minus_rho_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ_set z ⟨hz_in, hz_notin⟩
  rcases hden with ⟨hden_nz, hden_diff⟩
  have hz_le : ‖z‖ ≤ R1 := by
    simpa [Metric.closedBall, dist_eq_norm] using hz_in
  have hle1 : R1 < 1 := by linarith [hR1_lt_R, hR_lt_1]
  have hz_in1 : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have : ‖z‖ ≤ 1 := le_of_lt (hz_le.trans_lt hle1)
    simpa [Metric.closedBall, dist_eq_norm] using this
  have hz_inR : z ∈ Metric.closedBall (0 : ℂ) R := by
    have hz_le_R : ‖z‖ ≤ R := by
      calc ‖z‖ ≤ R1 := hz_le
      _ ≤  R := le_of_lt hR1_lt_R
    simpa [Metric.closedBall, dist_eq_norm] using hz_le_R
  have hnum := blaschke_num_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ_set z hz_inR
  rcases hnum with ⟨hnum_nz, hnum_diff⟩
  simpa using
    (logDerivdiv (hh := hnum_diff) (hg := hden_diff) (hh_ne := hnum_nz) (hg_ne := hden_nz))

lemma logDeriv_linear {a b : ℂ} {z : ℂ} (_ha : a ≠ 0) (_hz : z ≠ -b/a) :
    logDeriv (fun w ↦ a * w + b) z = a / (a * z + b) := by
                                 
  have h_id : HasDerivAt (fun w : ℂ => w) (1 : ℂ) z := hasDerivAt_id _
  have h_mul' : HasDerivAt (fun w : ℂ => a * w) a z := by
    simpa [one_mul] using (h_id.const_mul a)
  have h_deriv_mul : deriv (fun w : ℂ => a * w) z = a := h_mul'.deriv
                                
  simp [logDeriv]

lemma logDeriv_denominator {ρ : ℂ} {z : ℂ} (hz : z ≠ ρ) :
    logDeriv (fun w ↦ w - ρ) z = 1 / (z - ρ) := by
  have h :=
    logDeriv_linear (a := (1 : ℂ)) (b := -ρ) (z := z)
      (_ha := by simp)
      (_hz := by simpa using hz)
  simpa [one_mul, sub_eq_add_neg] using h

lemma logDeriv_numerator_pre {R : ℝ} {ρ : ℂ} {z : ℂ} :
    logDeriv (fun w ↦ R - (star ρ) * w / R) z = -(star ρ) / R / (R - (star ρ) * z / R) := by
  classical
                                                  
  let a : ℂ := -(star ρ) / (R : ℂ)
  let b : ℂ := (R : ℂ)
  have hlin : (fun w : ℂ ↦ (R : ℂ) - (star ρ) * w / (R : ℂ)) = (fun w : ℂ ↦ b + a * w) := by
    funext w
                         
    simp [a, b, sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm]
                                        
  have hderiv_add : deriv (fun w : ℂ => b + a * w) z =
      deriv (fun _ : ℂ => b) z + deriv (fun y : ℂ => a * y) z := by
    simp
  have hderiv_ab : deriv (fun w : ℂ => b + a * w) z = a := by
    simp [deriv_const, mul_comm]
                                                            
  simp [logDeriv, sub_eq_add_neg, div_eq_mul_inv,
         mul_comm, mul_left_comm, mul_assoc, add_comm]

lemma star_ne_zero_of_ne_zero {ρ : ℂ} (hρ : ρ ≠ 0) : star ρ ≠ 0 := by

  intro h
                                          
  have : ρ = 0 := (star_eq_zero).1 h
  exact hρ this

lemma field_identity_general {K : Type*} [Field K] {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (_hden : a - c*b/a ≠ 0) : (-(b/a)) / (a - c*b/a) = (1 : K) / (c - a^2/b) := by
                                               
  have hmul : (-(a / b) : K) ≠ 0 := by
    have hdiv_ne : a / b ≠ 0 := div_ne_zero ha hb
    exact neg_ne_zero.mpr hdiv_ne
  have hnum : (-(b/a) * (-(a/b))) = (1 : K) := by
    calc
      (-(b/a) * (-(a/b))) = (b/a) * (a/b) := by simp
      _ = (b * a⁻¹) * (a * b⁻¹) := by simp [div_eq_mul_inv]
      _ = b * (a⁻¹ * (a * b⁻¹)) := by simp [mul_assoc]
      _ = b * ((a⁻¹ * a) * b⁻¹) := by simp [mul_assoc]
      _ = b * (1 * b⁻¹) := by simp [ha]
      _ = b * b⁻¹ := by simp
      _ = 1 := by simp [hb]
  have hOne : (b/a) * (a/b) = (1 : K) := by
    calc
      (b/a) * (a/b) = (b * a⁻¹) * (a * b⁻¹) := by simp [div_eq_mul_inv]
      _ = b * (a⁻¹ * (a * b⁻¹)) := by simp [mul_assoc]
      _ = b * ((a⁻¹ * a) * b⁻¹) := by simp [mul_assoc]
      _ = b * (1 * b⁻¹) := by simp [ha]
      _ = b * b⁻¹ := by simp
      _ = 1 := by simp [hb]
  have haab : a * (a / b) = a^2 / b := by
    simp [div_eq_mul_inv, pow_two, mul_assoc]
  have hcbab : (c * b / a) * (a / b) = c := by
    calc
      (c * b / a) * (a / b) = (c * (b / a)) * (a / b) := by simp [div_eq_mul_inv, mul_assoc]
      _ = c * ((b / a) * (a / b)) := by simp [mul_assoc]
      _ = c * 1 := by simp [hOne]
      _ = c := by simp
  have hdenom : ((a - c*b/a) * (-(a/b))) = c - a^2 / b := by
    calc
      ((a - c*b/a) * (-(a/b))) = -((a - c*b/a) * (a / b)) := by simp [mul_neg]
      _ = -(a * (a / b) - (c * b / a) * (a / b)) := by simp [sub_mul]
      _ = (c * b / a) * (a / b) - a * (a / b) := by simp [neg_sub]
      _ = c - a^2 / b := by simp [hcbab, haab]
  calc
    (-(b/a)) / (a - c*b/a)
        = (-(b/a) * (-(a/b))) / ((a - c*b/a) * (-(a/b))) := by
          simpa using
            (mul_div_mul_right (a := (-(b / a))) (b := (a - c * b / a)) (c := (-(a / b))) hmul).symm
    _ = 1 / ((a - c*b/a) * (-(a/b))) := by simp [hnum]
    _ = 1 / (c - a^2/b) := by simp [hdenom]

lemma complex_identity_from_field {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0) (hρ : ρ ≠ 0) (hden : (R:ℂ) - (star ρ) * z / R ≠ 0) : (-(star ρ) / (R:ℂ)) / ((R:ℂ) - (star ρ) * z / R) = (1 : ℂ) / (z - (R:ℂ)^2 / (star ρ)) := by
  have ha : (R : ℂ) ≠ 0 := by simpa using (Complex.ofReal_ne_zero.mpr hR)
  have hb : star ρ ≠ 0 := star_ne_zero_of_ne_zero hρ
  have hden' : (R : ℂ) - z * (star ρ) / (R : ℂ) ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hden
  have h := field_identity_general (K := ℂ) (a := (R : ℂ)) (b := star ρ) (c := z) ha hb hden'
  simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h

lemma logDeriv_numerator_rearranged {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0) (hrho : ρ ≠ 0) (h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0) : -(star ρ) / R / ((R : ℂ) - (star ρ) * z / R) = 1 / (z - (R : ℂ)^2 / (star ρ)) := by
  simpa using (complex_identity_from_field (R:=R) (ρ:=ρ) (z:=z) (hR:=hR) (hρ:=hrho) (hden:=h_denom_ne_zero))

lemma logDeriv_numerator {R : ℝ} {ρ : ℂ} {z : ℂ}
    (hR : R ≠ 0)
    (hrho : ρ ≠ 0)
    (h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0):
    logDeriv (fun w ↦ R - (star ρ) * w / R) z = 1 / (z - R^2 / (star ρ)) := by
  rw [logDeriv_numerator_pre, logDeriv_numerator_rearranged]
  <;> assumption

lemma logDeriv_Blaschke_is_diff_frac {R R1 : ℝ} {f : ℂ → ℂ}
     (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) (h_f_zero : f 0 = 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ h_finite_zeros.toFinset,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f , logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z =
         1 / (z - R^2 / (star ρ)) - 1 / (z - ρ) := by
  intro ρ hρ z hz
                                                                         
  have h_div := logDeriv_Blaschke_is_diff (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz ρ hρ
                                                                     
  have hρ_mem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    exact (h_finite_zeros.mem_toFinset).mp hρ
  have hρ_ne_zero : ρ ≠ 0 := by
    intro h_eq
                                                            
    have : f 0 = 0 := by simpa [h_eq] using hρ_mem.2
    exact (zero_ne_one : (0 : ℂ) ≠ 1) (this.symm.trans h_f_zero)
  have hR_ne_zero : R ≠ 0 := ne_of_gt (hR1_pos.trans hR1_lt_R)
  have h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0 := by
                                                  
    have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R := by
      have hle : R1 < R := hR1_lt_R
      apply Metric.closedBall_subset_closedBall (le_of_lt hle)
      exact hz.1
    have h := blaschke_num_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ_mem z hz_ball
    exact h.1
  have h_num := logDeriv_numerator hR_ne_zero hρ_ne_zero h_denom_ne_zero
                                                        
  have hz_ne_rho : z ≠ ρ := by
    intro h_eq
    exact hz.2 (by simpa [h_eq] using hρ_mem)
  have h_den := logDeriv_denominator hz_ne_rho
                                
  rw [h_div, h_num, h_den]

lemma Lf_deriv_step3 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat * (1 / (z - R^2 / (star ρ)) - 1 / (z - ρ)) := by
  intro z hz
                                                          
  rw [Lf_deriv_step2 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  congr 1
  exact logDeriv_Blaschke_is_diff_frac hR1_pos hR1_lt_R hR_lt_1 h_f_zero h_f_analytic h_finite_zeros ρ hρ z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)


lemma sum_rearranged {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                    (1 / (z - R^2 / (star ρ)) - 1 / (z - ρ)) =
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) -
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) := by
  intro z hz
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext ρ
  rw [mul_sub, mul_one_div, mul_one_div]

lemma Lf_deriv_final_formula :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) +
                      ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) := by
  intro z hz
                                                               
  rw [Lf_deriv_step3 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz]
                                                  
  rw [sum_rearranged hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz]
                    
  ring

lemma rearrange_Lf_deriv :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) =
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z -
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) := by
  intro z hz
                                                                               
  have h_final := Lf_deriv_final_formula hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz
  rw [h_final]
  ring


lemma target_inequality_setup :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
  ‖deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
  ‖deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z‖ +
  ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ := by
  intro z hz

  have hrearr := rearrange_Lf_deriv hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz

  rw [hrearr]
  exact norm_sub_le _ _


lemma norm_div_eq (a b : ℂ) (_hb : b ≠ 0) : ‖a / b‖ = ‖a‖ / ‖b‖ := by
  calc
    ‖a / b‖ = ‖a * b⁻¹‖ := by simp [div_eq_mul_inv]
    _ = ‖a‖ * ‖b⁻¹‖ := norm_mul _ _
    _ = ‖a‖ * ‖b‖⁻¹ := by simp [norm_inv]
    _ = ‖a‖ / ‖b‖ := by simp [div_eq_mul_inv]

lemma norm_Rsq_div_conj (R : ℝ) (ρ : ℂ) (hρ : ρ ≠ 0) : ‖((R^2 : ℂ) / (star ρ))‖ = (R^2 : ℝ) / ‖ρ‖ := by
  have hb : star ρ ≠ 0 := by
    intro h
    have h' := congrArg star h
                                     
    have : ρ = 0 := by simpa [star_star] using h'
    exact hρ this
  have hnormR : ‖(R^2 : ℂ)‖ = (R^2 : ℝ) := by
    have h := (RCLike.norm_ofReal (K:=ℂ) (R^2))
    simp
  calc
    ‖((R^2 : ℂ) / (star ρ))‖
        = ‖(R^2 : ℂ)‖ / ‖star ρ‖ := norm_div_eq _ _ hb
    _ = (R^2 : ℝ) / ‖ρ‖ := by
      simp [hnormR]

lemma zerosetKfR_subset_closedBall {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ} :
  zerosetKfR R1 hR1 f ⊆ Metric.closedBall (0 : ℂ) R1 := by
  intro ρ hρ
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 ∧ f ρ = 0 := by
    simpa [zerosetKfR] using hρ
  exact hmem.left

lemma mem_zerosetKfR_ne_zero_of_f0_eq_one {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ}
  (hf0 : f 0 = 1) {ρ : ℂ} (hρ : ρ ∈ zerosetKfR R1 hR1 f) : ρ ≠ 0 := by
  intro hρ0
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 ∧ f ρ = 0 := by
    simpa [zerosetKfR] using hρ
  have hzero : f 0 = 0 := by simpa [hρ0] using hmem.right
  have h10 : (1 : ℂ) ≠ 0 := one_ne_zero
  exact h10 (by simp [hf0] at hzero)

lemma norm_sub_ge_norm_sub (x y : ℂ) : ‖x - y‖ ≥ ‖y‖ - ‖x‖ := by
  have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    simpa [sub_eq_add_neg, add_comm] using norm_add_le (y - x) x
  have h' : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := (sub_le_iff_le_add).mpr htri
  have hsymm : ‖y - x‖ = ‖x - y‖ := by
    simpa [sub_eq_add_neg, add_comm] using (norm_neg (x - y))
  simpa [hsymm] using h'

lemma mem_zerosetKfR_norm_le {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ} {ρ : ℂ}
  (hρ : ρ ∈ zerosetKfR R1 hR1 f) : ‖ρ‖ ≤ R1 := by
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 :=
    (zerosetKfR_subset_closedBall (R1 := R1) hR1 (f := f)) hρ
  have hdist : dist ρ (0 : ℂ) ≤ R1 := by
    simpa [Metric.mem_closedBall] using hmem
  simpa [dist_eq_norm, sub_zero] using hdist

lemma lem_sum_bound_step2 {R R1: ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
      (∑ ρ ∈ h_finite_zeros.toFinset,
          ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - (R^2 : ℂ) / (star ρ)‖)
        ≤ (1/(R^2/R1 - R1)) *
          (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) := by
  classical
  intro z hz
  rcases hz with ⟨hzball, _hznotin⟩
  have hz_norm : ‖z‖ ≤ R1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
                            
  set S := h_finite_zeros.toFinset
  have hS_spec : ∀ {ρ : ℂ}, ρ ∈ S → ρ ∈ zerosetKfR R1 (by linarith) f := by
    intro ρ hρ
    have hiff := (Set.Finite.mem_toFinset (hs := h_finite_zeros) : ρ ∈ S ↔ ρ ∈ zerosetKfR R1 (by linarith) f)
    exact (Iff.mp hiff) hρ
                                
  have hsum_le :
      (∑ ρ ∈ S, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - (R^2 : ℂ) / (star ρ)‖)
        ≤ ∑ ρ ∈ S, (1/(R^2/R1 - R1)) * ((analyticOrderAt f ρ).toNat : ℝ) := by
    refine Finset.sum_le_sum ?termwise
    intro ρ hρS
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f := hS_spec hρS
    have hρ_ne : ρ ≠ 0 :=
      mem_zerosetKfR_ne_zero_of_f0_eq_one (R1 := R1) (hR1 := by linarith)
        (f := f) h_f_zero hρmem
    have hρ_norm : ‖ρ‖ ≤ R1 := mem_zerosetKfR_norm_le (R1 := R1)
      (hR1 := by linarith) (f := f) hρmem
    have hpt : 1 / ‖z - (R^2 : ℂ) / (star ρ)‖ ≤ 1/(R^2/R1 - R1) := by
                                          
      have h_Rsq_norm : ‖((R^2 : ℂ) / (star ρ))‖ = (R^2 : ℝ) / ‖ρ‖ :=
        norm_Rsq_div_conj R ρ hρ_ne
      have h_lower_bound : ‖z - (R^2 : ℂ) / (star ρ)‖ ≥ ‖((R^2 : ℂ) / (star ρ))‖ - ‖z‖ :=
        norm_sub_ge_norm_sub z ((R^2 : ℂ) / (star ρ))
                                                                              
      have hρ_pos : 0 < ‖ρ‖ := by
        simpa [norm_pos_iff] using hρ_ne
      have h_Rsq_bound : R^2/R1 ≤ ‖((R^2 : ℂ) / (star ρ))‖ := by
        rw [h_Rsq_norm]
        exact div_le_div_of_nonneg_left (sq_nonneg R) hρ_pos hρ_norm
      have h_combined : R^2/R1 - R1 ≤ ‖z - (R^2 : ℂ) / (star ρ)‖ := by
        calc R^2/R1 - R1
        _ ≤ ‖((R^2 : ℂ) / (star ρ))‖ - R1 := by linarith [h_Rsq_bound]
        _ ≤ ‖((R^2 : ℂ) / (star ρ))‖ - ‖z‖ := by linarith [hz_norm]
        _ ≤ ‖z - (R^2 : ℂ) / (star ρ)‖ := h_lower_bound
      have h_pos_denom : 0 < R^2/R1 - R1 := by
        have h_R_pos : 0 < R := by linarith [hR1_pos, hR1_lt_R]
        have h_Rsq_pos : 0 < R^2 := sq_pos_of_pos h_R_pos
        calc R^2/R1 - R1
        _ = (R^2 - R1*R1)/R1 := by field_simp
        _ = (R - R1)*(R + R1)/R1 := by ring
        _ > 0 := by
          apply div_pos
          · apply mul_pos
            · linarith [hR1_lt_R]
            · linarith [hR1_pos, hR1_lt_R]
          · exact hR1_pos
      have h_pos_norm : 0 < ‖z - (R^2 : ℂ) / (star ρ)‖ := by
        apply lt_of_lt_of_le h_pos_denom h_combined
                                                              
      have h_reciprocal : 1 / ‖z - (R^2 : ℂ) / (star ρ)‖ ≤ 1 / (R^2/R1 - R1) := by
        apply div_le_div_of_nonneg_left
        · norm_num
        · exact h_pos_denom
        · exact h_combined
      exact h_reciprocal
    have hmnonneg : 0 ≤ ((analyticOrderAt f ρ).toNat : ℝ) := by
      exact_mod_cast (Nat.zero_le (analyticOrderAt f ρ).toNat)
    have hmul := mul_le_mul_of_nonneg_left hpt hmnonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
                                         
  rw [← Finset.mul_sum] at hsum_le
  exact hsum_le

lemma sq_div_sub_pos (a b : ℝ) (ha_pos : 0 < a) (hab : a < b) : 0 < b^2/a - a := by
                                        
  rw [sub_pos]
                                                        
  rw [lt_div_iff₀ ha_pos]
                         
  rw [← pow_two]
                                                                         
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  apply pow_lt_pow_left₀ hab ha_nonneg
  norm_num                                          

lemma final_sum_bound {R R1 B : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (hB : 1 < B)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ ≤
    1/((R^2/R1 - R1) * Real.log (R/R1)) * Real.log B := by
  intro z hz
                                                  
  have h_norm_bound := norm_sum_le h_finite_zeros.toFinset (fun ρ => (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)))

  have h_sum_eq : ∑ ρ ∈ h_finite_zeros.toFinset, ‖(analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ =
    ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - R^2 / (star ρ)‖ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [norm_div, Complex.norm_natCast]

  have h_step2 := lem_sum_bound_step2 hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz

  have h_f_nonzero : f 0 ≠ 0 := by rw [h_f_zero]; norm_num
  have h_f_bounded_alt : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B := by
    intro w hw
    exact h_f_bounded w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw))
                                                  
  have h_exists : ∀ σ : ℂ, ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g σ ∧ g σ ≠ 0 ∧
      (σ ∈ zerosetKfR R1 (by linarith) f →
        ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * g z) := by
    intro σ
    by_cases hσ : σ ∈ zerosetKfR R1 (by linarith) f
    ·                                             
      have hex := lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero σ hσ
      obtain ⟨g, hg_at, hg_ne, h_eq⟩ := hex
      exact ⟨g, hg_at, hg_ne, fun _ => h_eq⟩
    ·                                            
      refine ⟨fun _ => 1, ?_, ?_, ?_⟩
      · exact analyticAt_const
      · norm_num
      · intro h_contra
        contradiction
                                                 
  let h_σ : ℂ → (ℂ → ℂ) := fun σ => Classical.choose (h_exists σ)
  have h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z := by
    intro σ hσ
    have spec := Classical.choose_spec (h_exists σ)
    exact ⟨spec.1, spec.2.1, spec.2.2 hσ⟩
  have h_sum_bound := lem_sum_m_rho_bound B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero h_f_zero h_finite_zeros h_σ h_f_bounded_alt h_σ_spec

  have h_pos : 0 < R^2/R1 - R1 := sq_div_sub_pos R1 R hR1_pos hR1_lt_R
  have h_ratio_gt_one : 1 < R/R1 := by
    rw [one_lt_div_iff]
    left
    exact ⟨hR1_pos, hR1_lt_R⟩
  have h_log_pos : 0 < Real.log (R/R1) := Real.log_pos h_ratio_gt_one

  calc ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖
    ≤ ∑ ρ ∈ h_finite_zeros.toFinset, ‖(analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ := h_norm_bound
    _ = ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - R^2 / (star ρ)‖ := h_sum_eq
    _ ≤ (1/(R^2/R1 - R1)) * (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) := h_step2
    _ ≤ (1/(R^2/R1 - R1)) * ((1/Real.log (R/R1)) * Real.log B) := by
              apply mul_le_mul_of_nonneg_left h_sum_bound (div_nonneg zero_le_one (le_of_lt h_pos))
    _ = 1/((R^2/R1 - R1) * Real.log (R/R1)) * Real.log B := by
      field_simp [ne_of_gt h_pos, ne_of_gt h_log_pos]

lemma final_inequality
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic :
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ_spec :
      ∀ σ ∈ zerosetKfR R1 (by linarith) f,
        AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
        ∀ᶠ z in nhds σ,
          f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1 \ zerosetKfR R1 (by linarith) f,

        ‖(deriv f z / f z
          - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ))‖
      ≤
      16 * r^2 / ((r - r1)^3) * Real.log B
        + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) * Real.log B := by
  intro z hz

  have hr_pos : 0 < r := by linarith [hr1pos, hr1_lt_r]
  have hR1_pos : 0 < R1 := by linarith [hr_pos, hr_lt_R1]

  have hz_in_r : z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f := by
    constructor
    · apply Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_r)
      exact hz.1
    · exact hz.2

  have hineq :=
    target_inequality_setup hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz_in_r

  have hz_in_R1 : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f := by
    constructor
    · apply Metric.closedBall_subset_closedBall
      exact le_of_lt (lt_trans hr1_lt_r hr_lt_R1)
      exact hz.1
    · exact hz.2

  have hsum :=
    final_sum_bound hR1_pos hR1_lt_R hR_lt_1 hB h_f_analytic h_f_zero h_finite_zeros h_f_bounded z hz_in_R1

  have hz_le_r1 : ‖z‖ ≤ r1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.1

  have hz_abs : ‖z‖ ≤ r1 := hz_le_r1

  have h_BC := apply_BC_to_Lf
    (B := B) (r1 := r1) (r := r) (R := R) (R1 := R1)
    (hB := hB) (hr1_pos := hr1pos) (hr1_lt_r := hr1_lt_r) (hr_lt_R1 := hr_lt_R1)
    (hR1_pos := hR1_pos) (hR1_lt_R := hR1_lt_R) (hR_lt_1 := hR_lt_1)
    (f := f) (h_f_analytic := h_f_analytic) (h_f_zero := h_f_zero)
    (h_finite_zeros := h_finite_zeros) (h_σ := h_σ) (h_σ_spec := h_σ_spec)
    (h_f_bound := fun w hw => h_f_bounded w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw)))
    z hz_abs

  have hLf : ‖deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z‖ ≤
             16 * r^2 / ((r - r1)^3) * Real.log B := by

    convert (preTransparency := .instances) h_BC using 1
                                                                                             
    ring

  exact le_trans hineq (add_le_add hLf hsum)

lemma final_ineq1
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1 \ zerosetKfR R1 (by linarith) f,
    ‖(deriv f z / f z) - ∑ ρ ∈ h_finite_zeros.toFinset,
                 (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
    (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log B := by
  intro z hz
                                                            
  have h_bound : ‖(deriv f z / f z) - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
      16 * r^2 / ((r - r1)^3) * Real.log B + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) * Real.log B := by
    apply final_inequality <;> assumption
                                                                                  
  rw [← add_mul] at h_bound
  exact h_bound

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTAdaptiveDisk
namespace OAI

/-! A local analytic disk estimate with an explicit logarithmic growth budget.
The statement is independent of the physical radius, so it can be used on the
shrinking disks required by a Vinogradov--Korobov growth estimate. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter
open scoped _root_.BigOperators _root_.Classical _root_.Topology



private lemma mrt_disk_factorization (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) :
    ∃ g : ℂ → ℂ → ℂ, ∀ ρ ∈ mrtDiskZeros f,
      AnalyticAt ℂ (g ρ) ρ ∧ g ρ ρ ≠ 0 ∧
        ∀ᶠ w in 𝓝 ρ, f w = (w - ρ) ^ (analyticOrderAt f ρ).toNat * g ρ w := by
  have hfactor : ∀ ρ : ℂ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      (ρ ∈ mrtDiskZeros f →
        ∀ᶠ w in 𝓝 ρ, f w = (w - ρ) ^ (analyticOrderAt f ρ).toNat * g w) := by
    intro ρ
    by_cases hρ : ρ ∈ mrtDiskZeros f
    · obtain ⟨g, hg, hgne, heq⟩ := Erdos970.lem_analytic_zero_factor
        (15 / 16) (7 / 8) (by norm_num) (by norm_num) (by norm_num) f hf
        (by rw [h0]; exact one_ne_zero) ρ hρ
      exact ⟨g, hg, hgne, fun _ => heq⟩
    · exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, fun h => (hρ h).elim⟩
  exact ⟨fun ρ => Classical.choose (hfactor ρ), fun ρ hρ =>
    ⟨(Classical.choose_spec (hfactor ρ)).1,
      (Classical.choose_spec (hfactor ρ)).2.1,
      (Classical.choose_spec (hfactor ρ)).2.2 hρ⟩⟩

/-- Logarithmic derivative equals the actual finite zero sum with an error
linear in the logarithmic growth budget. -/
theorem mrt_disk_logderiv_oai (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16), ‖f z‖ ≤ Real.exp B)
    {z : ℂ} (hz : ‖z‖ ≤ 3 / 4) (hn : f z ≠ 0) :
    ‖deriv f z / f z -
      ∑ ρ ∈ (mrtDiskZeros_finite f hf h0).toFinset,
        (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
      mrtCharacterLogDerivativeConstant * B := by
  obtain ⟨g, hg⟩ := mrt_disk_factorization f hf h0
  have hz' : z ∈ Metric.closedBall (0 : ℂ) (3 / 4 : ℝ) \
      Erdos970.zerosetKfR (7 / 8) (by norm_num) f :=
    ⟨by simpa using hz, fun h => hn h.2⟩
  have h := Erdos970.final_ineq1 (Real.exp B) (Real.one_lt_exp_iff.mpr hB)
    (3 / 4) (4 / 5) (15 / 16) (7 / 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    f hf h0 (mrtDiskZeros_finite f hf h0) hg hbound z hz'
  simpa only [mrtDiskZeros, Real.log_exp, mrtCharacterLogDerivativeConstant] using h



end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_disk_logderiv_oai := @OAI.TwoPointCorrelations.mrt_disk_logderiv_oai
