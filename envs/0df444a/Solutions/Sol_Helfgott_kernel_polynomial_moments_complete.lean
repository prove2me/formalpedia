-- Prove2me | solution 1 for Helfgott.kernel_polynomial_moments_complete
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T02:23:22.565016+00:00
-- url     : https://prove2.me/submissions/1b3dd81b-84e5-48ed-83d3-cda45a304695

import Definitions.Def_Helfgott_KernelPolynomialMoments
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Set

namespace Helfgott

noncomputable def kernelMassPolynomialExact (t : ℝ) : ℝ := t*(2-t)^3
noncomputable def kernelMassPrimitiveExact (t : ℝ) : ℝ :=
  (-t^4+10*t^3-42*t^2+92*t-92)*Real.exp (t-1/2)

lemma kernelMassPrimitiveExact_hasDerivAt (t : ℝ) :
    HasDerivAt kernelMassPrimitiveExact (kernelMassPolynomialExact t*Real.exp (t-1/2)) t := by
  have hp : HasDerivAt (fun t : ℝ => -t^4+10*t^3-42*t^2+92*t-92)
      (-4*t^3+30*t^2-84*t+92) t := by
    convert! (((((hasDerivAt_id t).pow 4).neg.add
      (((hasDerivAt_id t).pow 3).const_mul 10)).sub
      (((hasDerivAt_id t).pow 2).const_mul 42)).add
      ((hasDerivAt_id t).const_mul 92)).sub_const 92 using 1 <;> simp only [id_eq] <;> ring
  have he := ((hasDerivAt_id t).sub_const (1/2 : ℝ)).exp
  convert! hp.mul he using 1 <;> simp only [kernelMassPrimitiveExact,kernelMassPolynomialExact,id_eq,Pi.mul_apply] <;> ring

lemma kernel_mass_whole_interval_exact :
    (∫ t in (0 : ℝ)..2,|kernelMassPolynomialExact t| *Real.exp (t-1/2))≤5/2 := by
  have hc : Continuous (fun t : ℝ => kernelMassPolynomialExact t*Real.exp (t-1/2)) := by
    unfold kernelMassPolynomialExact; fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => kernelMassPrimitiveExact_hasDerivAt t) (hc.intervalIntegrable 0 2)
  have hab : (∫ t in (0 : ℝ)..2,|kernelMassPolynomialExact t| *Real.exp (t-1/2))=
      ∫ t in (0 : ℝ)..2,kernelMassPolynomialExact t*Real.exp (t-1/2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ)≤2)] at ht
    have hta : 0≤t := ht.1
    have htb : 0≤2-t := by linarith [ht.2]
    dsimp only
    rw [abs_of_nonneg (show 0≤kernelMassPolynomialExact t by unfold kernelMassPolynomialExact; positivity)]
  rw [hab,hi]
  have he2 : (59/8 : ℝ)≤Real.exp 2 := by
    have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤2) 10
    norm_num [Finset.sum_range_succ] at hh
    linarith
  have hehalf : (7/5 : ℝ)≤Real.exp (1/2) := by
    have hh := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤1/2)
    norm_num at hh
    linarith
  have hinv : Real.exp (-(1/2 : ℝ))≤5/7 := by
    rw [Real.exp_neg,inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  have he : Real.exp (3/2 : ℝ)=Real.exp (-(1/2 : ℝ))*Real.exp 2 := by
    rw [←Real.exp_add]; congr 1; norm_num
  norm_num [kernelMassPrimitiveExact] at *
  rw [he]
  have hh := mul_le_mul_of_nonneg_left he2 (Real.exp_nonneg (-(1/2 : ℝ)))
  nlinarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 5000
open MeasureTheory Set Finset

namespace Helfgott

noncomputable def kernelMassPolynomial (t : ℝ) : ℝ := t*(2-t)^3
noncomputable def kernelVariationPolynomial (t : ℝ) : ℝ := t*(2-t)*(16-26*t-3*t^2+7*t^3+t^4)

lemma exp_sixteenth_rational_upper : Real.exp (1/16 : ℝ)≤16/15 := by
  have hh := Real.exp_le_two_add_div_two_sub (by norm_num : (0 : ℝ)≤1/16)
    (by norm_num : (1/16 : ℝ)<2)
  norm_num at hh
  linarith

lemma exp_mesh_rational_upper (t : ℝ) (m : ℕ) (ht : t≤(m : ℝ)/16) :
    Real.exp t≤(16/15 : ℝ)^m := by
  calc
    _≤Real.exp ((m : ℝ)/16) := Real.exp_le_exp.mpr ht
    _=(Real.exp (1/16 : ℝ))^m := by rw [← Real.exp_nat_mul]; congr 1; ring
    _≤_ := pow_le_pow_left₀ (Real.exp_nonneg _) exp_sixteenth_rational_upper m

lemma interval_mass_of_mesh_bound (p : ℝ → ℝ) (hp : Continuous p) (a b M E : ℝ)
    (hab : a≤b) (hM : 0≤M) (hb : ∀ t ∈ Icc a b,|p t|≤M)
    (he : ∀ t ∈ Icc a b,Real.exp (t-1/2)≤E) :
    (∫ t in a..b,|p t| * Real.exp (t-1/2))≤(b-a)*M*E := by
  have hf : Continuous (fun t => |p t| * Real.exp (t-1/2)) := by fun_prop
  have hh := intervalIntegral.integral_mono_on (μ := volume) hab (hf.intervalIntegrable a b)
    (intervalIntegrable_const (b := b) (a := a) (c := M*E))
    (fun t ht => mul_le_mul (hb t ht) (he t ht) (Real.exp_nonneg _) hM)
  simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_assoc] using hh

lemma kernel_variation_mesh_0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(29184175/16777216 : ℝ) := by
  have hta : 0≤t-(0 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(29184175/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(29184175/16777216 : ℝ)=(29184175 : ℝ)*(t-(0 : ℝ))^0*((1/16 : ℝ)-t)^6 + (208659482 : ℝ)*(t-(0 : ℝ))^1*((1/16 : ℝ)-t)^5 + (601078337 : ℝ)*(t-(0 : ℝ))^2*((1/16 : ℝ)-t)^4 + (901483948 : ℝ)*(t-(0 : ℝ))^3*((1/16 : ℝ)-t)^3 + (746818369 : ℝ)*(t-(0 : ℝ))^4*((1/16 : ℝ)-t)^2 + (325305802 : ℝ)*(t-(0 : ℝ))^5*((1/16 : ℝ)-t)^1 + (58368350 : ℝ)*(t-(0 : ℝ))^6*((1/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(29184175/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (29184175/16777216 : ℝ)-kernelVariationPolynomial t=(29184175 : ℝ)*(t-(0 : ℝ))^0*((1/16 : ℝ)-t)^6 + (141550618 : ℝ)*(t-(0 : ℝ))^1*((1/16 : ℝ)-t)^5 + (274446913 : ℝ)*(t-(0 : ℝ))^2*((1/16 : ℝ)-t)^4 + (265883052 : ℝ)*(t-(0 : ℝ))^3*((1/16 : ℝ)-t)^3 + (128706881 : ℝ)*(t-(0 : ℝ))^4*((1/16 : ℝ)-t)^2 + (24904298 : ℝ)*(t-(0 : ℝ))^5*((1/16 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_0 :
    (∫ t in (0 : ℝ)..(1/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(29184175/268435456 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (0 : ℝ) (1/16 : ℝ) (29184175/16777216 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_0 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_1 (t : ℝ) (ht : t ∈ Icc (1/16 : ℝ) (1/8 : ℝ)) :
    |kernelVariationPolynomial t|≤(781335/262144 : ℝ) := by
  have hta : 0≤t-(1/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(781335/262144 : ℝ) := by
    rw [show kernelVariationPolynomial t+(781335/262144 : ℝ)=(79189615 : ℝ)*(t-(1/16 : ℝ))^0*((1/8 : ℝ)-t)^6 + (500041988 : ℝ)*(t-(1/16 : ℝ))^1*((1/8 : ℝ)-t)^5 + (1308180324 : ℝ)*(t-(1/16 : ℝ))^2*((1/8 : ℝ)-t)^4 + (1816192224 : ℝ)*(t-(1/16 : ℝ))^3*((1/8 : ℝ)-t)^3 + (1412074320 : ℝ)*(t-(1/16 : ℝ))^4*((1/8 : ℝ)-t)^2 + (583220928 : ℝ)*(t-(1/16 : ℝ))^5*((1/8 : ℝ)-t)^1 + (100010880 : ℝ)*(t-(1/16 : ℝ))^6*((1/8 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(781335/262144 : ℝ)-kernelVariationPolynomial t := by
    rw [show (781335/262144 : ℝ)-kernelVariationPolynomial t=(20821265 : ℝ)*(t-(1/16 : ℝ))^0*((1/8 : ℝ)-t)^6 + (100023292 : ℝ)*(t-(1/16 : ℝ))^1*((1/8 : ℝ)-t)^5 + (191982876 : ℝ)*(t-(1/16 : ℝ))^2*((1/8 : ℝ)-t)^4 + (184025376 : ℝ)*(t-(1/16 : ℝ))^3*((1/8 : ℝ)-t)^3 + (88088880 : ℝ)*(t-(1/16 : ℝ))^4*((1/8 : ℝ)-t)^2 + (16844352 : ℝ)*(t-(1/16 : ℝ))^5*((1/8 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_1 :
    (∫ t in (1/16 : ℝ)..(1/8 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(781335/4194304 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (1/16 : ℝ) (1/8 : ℝ) (781335/262144 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_1 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_2 (t : ℝ) (ht : t ∈ Icc (1/8 : ℝ) (3/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(63099447/16777216 : ℝ) := by
  have hta : 0≤t-(1/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(3/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(63099447/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(63099447/16777216 : ℝ)=(113104887 : ℝ)*(t-(1/8 : ℝ))^0*((3/16 : ℝ)-t)^6 + (695473674 : ℝ)*(t-(1/8 : ℝ))^1*((3/16 : ℝ)-t)^5 + (1776927945 : ℝ)*(t-(1/8 : ℝ))^2*((3/16 : ℝ)-t)^4 + (2415186156 : ℝ)*(t-(1/8 : ℝ))^3*((3/16 : ℝ)-t)^3 + (1842157725 : ℝ)*(t-(1/8 : ℝ))^4*((3/16 : ℝ)-t)^2 + (747729622 : ℝ)*(t-(1/8 : ℝ))^5*((3/16 : ℝ)-t)^1 + (126198894 : ℝ)*(t-(1/8 : ℝ))^6*((3/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(63099447/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (63099447/16777216 : ℝ)-kernelVariationPolynomial t=(13094007 : ℝ)*(t-(1/8 : ℝ))^0*((3/16 : ℝ)-t)^6 + (61719690 : ℝ)*(t-(1/8 : ℝ))^1*((3/16 : ℝ)-t)^5 + (116055465 : ℝ)*(t-(1/8 : ℝ))^2*((3/16 : ℝ)-t)^4 + (108791724 : ℝ)*(t-(1/8 : ℝ))^3*((3/16 : ℝ)-t)^3 + (50825685 : ℝ)*(t-(1/8 : ℝ))^4*((3/16 : ℝ)-t)^2 + (9463742 : ℝ)*(t-(1/8 : ℝ))^5*((3/16 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_2 :
    (∫ t in (1/8 : ℝ)..(3/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(63099447/268435456 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (1/8 : ℝ) (3/16 : ℝ) (63099447/16777216 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_2 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_3 (t : ℝ) (ht : t ∈ Icc (3/16 : ℝ) (1/4 : ℝ)) :
    |kernelVariationPolynomial t|≤(16891/4096 : ℝ) := by
  have hta : 0≤t-(3/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1/4 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(16891/4096 : ℝ) := by
    rw [show kernelVariationPolynomial t+(16891/4096 : ℝ)=(132284983 : ℝ)*(t-(3/16 : ℝ))^0*((1/4 : ℝ)-t)^6 + (803173640 : ℝ)*(t-(3/16 : ℝ))^1*((1/4 : ℝ)-t)^5 + (2028086480 : ℝ)*(t-(3/16 : ℝ))^2*((1/4 : ℝ)-t)^4 + (2726435584 : ℝ)*(t-(3/16 : ℝ))^3*((1/4 : ℝ)-t)^3 + (2058252544 : ℝ)*(t-(3/16 : ℝ))^4*((1/4 : ℝ)-t)^2 + (827385856 : ℝ)*(t-(3/16 : ℝ))^5*((1/4 : ℝ)-t)^1 + (138371072 : ℝ)*(t-(3/16 : ℝ))^6*((1/4 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(16891/4096 : ℝ)-kernelVariationPolynomial t := by
    rw [show (16891/4096 : ℝ)-kernelVariationPolynomial t=(6086089 : ℝ)*(t-(3/16 : ℝ))^0*((1/4 : ℝ)-t)^6 + (27052792 : ℝ)*(t-(3/16 : ℝ))^1*((1/4 : ℝ)-t)^5 + (47479600 : ℝ)*(t-(3/16 : ℝ))^2*((1/4 : ℝ)-t)^4 + (40985856 : ℝ)*(t-(3/16 : ℝ))^3*((1/4 : ℝ)-t)^3 + (17313536 : ℝ)*(t-(3/16 : ℝ))^4*((1/4 : ℝ)-t)^2 + (2840576 : ℝ)*(t-(3/16 : ℝ))^5*((1/4 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_3 :
    (∫ t in (3/16 : ℝ)..(1/4 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(16891/65536 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (3/16 : ℝ) (1/4 : ℝ) (16891/4096 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_3 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_4 (t : ℝ) (ht : t ∈ Icc (1/4 : ℝ) (5/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(5468013/1310720 : ℝ) := by
  have hta : 0≤t-(1/4 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(5/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(5468013/1310720 : ℝ) := by
    rw [show kernelVariationPolynomial t+(5468013/1310720 : ℝ)=(695880512/5 : ℝ)*(t-(1/4 : ℝ))^0*((5/16 : ℝ)-t)^6 + (4189485952/5 : ℝ)*(t-(1/4 : ℝ))^1*((5/16 : ℝ)-t)^5 + (2098733760 : ℝ)*(t-(1/4 : ℝ))^2*((5/16 : ℝ)-t)^4 + (2799622656 : ℝ)*(t-(1/4 : ℝ))^3*((5/16 : ℝ)-t)^3 + (2097798288 : ℝ)*(t-(1/4 : ℝ))^4*((5/16 : ℝ)-t)^2 + (4186171032/5 : ℝ)*(t-(1/4 : ℝ))^5*((5/16 : ℝ)-t)^1 + (695229507/5 : ℝ)*(t-(1/4 : ℝ))^6*((5/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(5468013/1310720 : ℝ)-kernelVariationPolynomial t := by
    rw [show (5468013/1310720 : ℝ)-kernelVariationPolynomial t=(4025152/5 : ℝ)*(t-(1/4 : ℝ))^0*((5/16 : ℝ)-t)^6 + (9948032/5 : ℝ)*(t-(1/4 : ℝ))^1*((5/16 : ℝ)-t)^5 + (983232 : ℝ)*(t-(1/4 : ℝ))^2*((5/16 : ℝ)-t)^4 + (1918704 : ℝ)*(t-(1/4 : ℝ))^4*((5/16 : ℝ)-t)^2 + (13262952/5 : ℝ)*(t-(1/4 : ℝ))^5*((5/16 : ℝ)-t)^1 + (4676157/5 : ℝ)*(t-(1/4 : ℝ))^6*((5/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_4 :
    (∫ t in (1/4 : ℝ)..(5/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(5468013/20971520 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (1/4 : ℝ) (5/16 : ℝ) (5468013/1310720 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_4 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_5 (t : ℝ) (ht : t ∈ Icc (5/16 : ℝ) (3/8 : ℝ)) :
    |kernelVariationPolynomial t|≤(69055335/16777216 : ℝ) := by
  have hta : 0≤t-(5/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(3/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(69055335/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(69055335/16777216 : ℝ)=(138110670 : ℝ)*(t-(5/16 : ℝ))^0*((3/8 : ℝ)-t)^6 + (825705222 : ℝ)*(t-(5/16 : ℝ))^1*((3/8 : ℝ)-t)^5 + (2054181837 : ℝ)*(t-(5/16 : ℝ))^2*((3/8 : ℝ)-t)^4 + (2722034988 : ℝ)*(t-(5/16 : ℝ))^3*((3/8 : ℝ)-t)^3 + (2026408089 : ℝ)*(t-(5/16 : ℝ))^4*((3/8 : ℝ)-t)^2 + (803576362 : ℝ)*(t-(5/16 : ℝ))^5*((3/8 : ℝ)-t)^1 + (132615975 : ℝ)*(t-(5/16 : ℝ))^6*((3/8 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(69055335/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (69055335/16777216 : ℝ)-kernelVariationPolynomial t=(2958798 : ℝ)*(t-(5/16 : ℝ))^1*((3/8 : ℝ)-t)^5 + (17478213 : ℝ)*(t-(5/16 : ℝ))^2*((3/8 : ℝ)-t)^4 + (40178412 : ℝ)*(t-(5/16 : ℝ))^3*((3/8 : ℝ)-t)^3 + (45251961 : ℝ)*(t-(5/16 : ℝ))^4*((3/8 : ℝ)-t)^2 + (25087658 : ℝ)*(t-(5/16 : ℝ))^5*((3/8 : ℝ)-t)^1 + (5494695 : ℝ)*(t-(5/16 : ℝ))^6*((3/8 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_5 :
    (∫ t in (5/16 : ℝ)..(3/8 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(69055335/268435456 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (5/16 : ℝ) (3/8 : ℝ) (69055335/16777216 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_5 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_6 (t : ℝ) (ht : t ∈ Icc (3/8 : ℝ) (7/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(993135/262144 : ℝ) := by
  have hta : 0≤t-(3/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(7/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(993135/262144 : ℝ) := by
    rw [show kernelVariationPolynomial t+(993135/262144 : ℝ)=(127121280 : ℝ)*(t-(3/8 : ℝ))^0*((7/16 : ℝ)-t)^6 + (754847168 : ℝ)*(t-(3/8 : ℝ))^1*((7/16 : ℝ)-t)^5 + (1865182544 : ℝ)*(t-(3/8 : ℝ))^2*((7/16 : ℝ)-t)^4 + (2454837344 : ℝ)*(t-(3/8 : ℝ))^3*((7/16 : ℝ)-t)^3 + (1815070660 : ℝ)*(t-(3/8 : ℝ))^4*((7/16 : ℝ)-t)^2 + (714851188 : ℝ)*(t-(3/8 : ℝ))^5*((7/16 : ℝ)-t)^1 + (117161215 : ℝ)*(t-(3/8 : ℝ))^6*((7/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(993135/262144 : ℝ)-kernelVariationPolynomial t := by
    rw [show (993135/262144 : ℝ)-kernelVariationPolynomial t=(7880512 : ℝ)*(t-(3/8 : ℝ))^1*((7/16 : ℝ)-t)^5 + (41636656 : ℝ)*(t-(3/8 : ℝ))^2*((7/16 : ℝ)-t)^4 + (87588256 : ℝ)*(t-(3/8 : ℝ))^3*((7/16 : ℝ)-t)^3 + (91748540 : ℝ)*(t-(3/8 : ℝ))^4*((7/16 : ℝ)-t)^2 + (47876492 : ℝ)*(t-(3/8 : ℝ))^5*((7/16 : ℝ)-t)^1 + (9960065 : ℝ)*(t-(3/8 : ℝ))^6*((7/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_6 :
    (∫ t in (3/8 : ℝ)..(7/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(993135/4194304 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (3/8 : ℝ) (7/16 : ℝ) (993135/262144 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_6 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_7 (t : ℝ) (ht : t ∈ Icc (7/16 : ℝ) (1/2 : ℝ)) :
    |kernelVariationPolynomial t|≤(53600575/16777216 : ℝ) := by
  have hta : 0≤t-(7/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1/2 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(53600575/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(53600575/16777216 : ℝ)=(107201150 : ℝ)*(t-(7/16 : ℝ))^0*((1/2 : ℝ)-t)^6 + (631323002 : ℝ)*(t-(7/16 : ℝ))^1*((1/2 : ℝ)-t)^5 + (1546830705 : ℝ)*(t-(7/16 : ℝ))^2*((1/2 : ℝ)-t)^4 + (2018273516 : ℝ)*(t-(7/16 : ℝ))^3*((1/2 : ℝ)-t)^3 + (1479049905 : ℝ)*(t-(7/16 : ℝ))^4*((1/2 : ℝ)-t)^2 + (577193850 : ℝ)*(t-(7/16 : ℝ))^5*((1/2 : ℝ)-t)^1 + (93708607 : ℝ)*(t-(7/16 : ℝ))^6*((1/2 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(53600575/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (53600575/16777216 : ℝ)-kernelVariationPolynomial t=(11883898 : ℝ)*(t-(7/16 : ℝ))^1*((1/2 : ℝ)-t)^5 + (61186545 : ℝ)*(t-(7/16 : ℝ))^2*((1/2 : ℝ)-t)^4 + (125749484 : ℝ)*(t-(7/16 : ℝ))^3*((1/2 : ℝ)-t)^3 + (128967345 : ℝ)*(t-(7/16 : ℝ))^4*((1/2 : ℝ)-t)^2 + (66013050 : ℝ)*(t-(7/16 : ℝ))^5*((1/2 : ℝ)-t)^1 + (13492543 : ℝ)*(t-(7/16 : ℝ))^6*((1/2 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_7 :
    (∫ t in (7/16 : ℝ)..(1/2 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(53600575/268435456 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (7/16 : ℝ) (1/2 : ℝ) (53600575/16777216 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_7 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_8 (t : ℝ) (ht : t ∈ Icc (1/2 : ℝ) (9/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(153/64 : ℝ) := by
  have hta : 0≤t-(1/2 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(9/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(153/64 : ℝ) := by
    rw [show kernelVariationPolynomial t+(153/64 : ℝ)=(80216064 : ℝ)*(t-(1/2 : ℝ))^0*((9/16 : ℝ)-t)^6 + (466354176 : ℝ)*(t-(1/2 : ℝ))^1*((9/16 : ℝ)-t)^5 + (1127239680 : ℝ)*(t-(1/2 : ℝ))^2*((9/16 : ℝ)-t)^4 + (1449897984 : ℝ)*(t-(1/2 : ℝ))^3*((9/16 : ℝ)-t)^3 + (1046556864 : ℝ)*(t-(1/2 : ℝ))^4*((9/16 : ℝ)-t)^2 + (401903872 : ℝ)*(t-(1/2 : ℝ))^5*((9/16 : ℝ)-t)^1 + (64143423 : ℝ)*(t-(1/2 : ℝ))^6*((9/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(153/64 : ℝ)-kernelVariationPolynomial t := by
    rw [show (153/64 : ℝ)-kernelVariationPolynomial t=(14942208 : ℝ)*(t-(1/2 : ℝ))^1*((9/16 : ℝ)-t)^5 + (76001280 : ℝ)*(t-(1/2 : ℝ))^2*((9/16 : ℝ)-t)^4 + (154423296 : ℝ)*(t-(1/2 : ℝ))^3*((9/16 : ℝ)-t)^3 + (156684096 : ℝ)*(t-(1/2 : ℝ))^4*((9/16 : ℝ)-t)^2 + (79392512 : ℝ)*(t-(1/2 : ℝ))^5*((9/16 : ℝ)-t)^1 + (16072641 : ℝ)*(t-(1/2 : ℝ))^6*((9/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_8 :
    (∫ t in (1/2 : ℝ)..(9/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(51/320 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (1/2 : ℝ) (9/16 : ℝ) (153/64 : ℝ) (16/15 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_8 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 1 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_9 (t : ℝ) (ht : t ∈ Icc (9/16 : ℝ) (5/8 : ℝ)) :
    |kernelVariationPolynomial t|≤(24035391/16777216 : ℝ) := by
  have hta : 0≤t-(9/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(5/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(24035391/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(24035391/16777216 : ℝ)=(48070782 : ℝ)*(t-(9/16 : ℝ))^0*((5/8 : ℝ)-t)^6 + (271381358 : ℝ)*(t-(9/16 : ℝ))^1*((5/8 : ℝ)-t)^5 + (635033909 : ℝ)*(t-(9/16 : ℝ))^2*((5/8 : ℝ)-t)^4 + (787896908 : ℝ)*(t-(9/16 : ℝ))^3*((5/8 : ℝ)-t)^3 + (546238657 : ℝ)*(t-(9/16 : ℝ))^4*((5/8 : ℝ)-t)^2 + (200439994 : ℝ)*(t-(9/16 : ℝ))^5*((5/8 : ℝ)-t)^1 + (30374911 : ℝ)*(t-(9/16 : ℝ))^6*((5/8 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(24035391/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (24035391/16777216 : ℝ)-kernelVariationPolynomial t=(17043334 : ℝ)*(t-(9/16 : ℝ))^1*((5/8 : ℝ)-t)^5 + (86027821 : ℝ)*(t-(9/16 : ℝ))^2*((5/8 : ℝ)-t)^4 + (173518732 : ℝ)*(t-(9/16 : ℝ))^3*((5/8 : ℝ)-t)^3 + (174823073 : ℝ)*(t-(9/16 : ℝ))^4*((5/8 : ℝ)-t)^2 + (87984698 : ℝ)*(t-(9/16 : ℝ))^5*((5/8 : ℝ)-t)^1 + (17695871 : ℝ)*(t-(9/16 : ℝ))^6*((5/8 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_9 :
    (∫ t in (9/16 : ℝ)..(5/8 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(2670599/26214400 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (9/16 : ℝ) (5/8 : ℝ) (24035391/16777216 : ℝ) (256/225 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_9 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 2 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_10 (t : ℝ) (ht : t ∈ Icc (5/8 : ℝ) (11/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(12033945/16777216 : ℝ) := by
  have hta : 0≤t-(5/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(11/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(12033945/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(12033945/16777216 : ℝ)=(18373465 : ℝ)*(t-(5/8 : ℝ))^0*((11/16 : ℝ)-t)^6 + (92050262 : ℝ)*(t-(5/8 : ℝ))^1*((11/16 : ℝ)-t)^5 + (184311687 : ℝ)*(t-(5/8 : ℝ))^2*((11/16 : ℝ)-t)^4 + (184369428 : ℝ)*(t-(5/8 : ℝ))^3*((11/16 : ℝ)-t)^3 + (92137659 : ℝ)*(t-(5/8 : ℝ))^4*((11/16 : ℝ)-t)^2 + (18403122 : ℝ)*(t-(5/8 : ℝ))^5*((11/16 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(12033945/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (12033945/16777216 : ℝ)-kernelVariationPolynomial t=(5694425 : ℝ)*(t-(5/8 : ℝ))^0*((11/16 : ℝ)-t)^6 + (52357078 : ℝ)*(t-(5/8 : ℝ))^1*((11/16 : ℝ)-t)^5 + (176706663 : ℝ)*(t-(5/8 : ℝ))^2*((11/16 : ℝ)-t)^4 + (296988372 : ℝ)*(t-(5/8 : ℝ))^3*((11/16 : ℝ)-t)^3 + (268880691 : ℝ)*(t-(5/8 : ℝ))^4*((11/16 : ℝ)-t)^2 + (126004218 : ℝ)*(t-(5/8 : ℝ))^5*((11/16 : ℝ)-t)^1 + (24067890 : ℝ)*(t-(5/8 : ℝ))^6*((11/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_10 :
    (∫ t in (5/8 : ℝ)..(11/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(267421/4915200 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (5/8 : ℝ) (11/16 : ℝ) (12033945/16777216 : ℝ) (4096/3375 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_10 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 3 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_11 (t : ℝ) (ht : t ∈ Icc (11/16 : ℝ) (3/4 : ℝ)) :
    |kernelVariationPolynomial t|≤(7365/4096 : ℝ) := by
  have hta : 0≤t-(11/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(3/4 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(7365/4096 : ℝ) := by
    rw [show kernelVariationPolynomial t+(7365/4096 : ℝ)=(18133095 : ℝ)*(t-(11/16 : ℝ))^0*((3/4 : ℝ)-t)^6 + (90395448 : ℝ)*(t-(11/16 : ℝ))^1*((3/4 : ℝ)-t)^5 + (180102864 : ℝ)*(t-(11/16 : ℝ))^2*((3/4 : ℝ)-t)^4 + (179268864 : ℝ)*(t-(11/16 : ℝ))^3*((3/4 : ℝ)-t)^3 + (89145600 : ℝ)*(t-(11/16 : ℝ))^4*((3/4 : ℝ)-t)^2 + (17717248 : ℝ)*(t-(11/16 : ℝ))^5*((3/4 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(7365/4096 : ℝ)-kernelVariationPolynomial t := by
    rw [show (7365/4096 : ℝ)-kernelVariationPolynomial t=(42200985 : ℝ)*(t-(11/16 : ℝ))^0*((3/4 : ℝ)-t)^6 + (271609032 : ℝ)*(t-(11/16 : ℝ))^1*((3/4 : ℝ)-t)^5 + (724908336 : ℝ)*(t-(11/16 : ℝ))^2*((3/4 : ℝ)-t)^4 + (1027412736 : ℝ)*(t-(11/16 : ℝ))^3*((3/4 : ℝ)-t)^3 + (815865600 : ℝ)*(t-(11/16 : ℝ))^4*((3/4 : ℝ)-t)^2 + (344287232 : ℝ)*(t-(11/16 : ℝ))^5*((3/4 : ℝ)-t)^1 + (60334080 : ℝ)*(t-(11/16 : ℝ))^6*((3/4 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_11 :
    (∫ t in (11/16 : ℝ)..(3/4 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(491/3375 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (11/16 : ℝ) (3/4 : ℝ) (7365/4096 : ℝ) (65536/50625 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_11 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 4 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_12 (t : ℝ) (ht : t ∈ Icc (3/4 : ℝ) (13/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(47186633/16777216 : ℝ) := by
  have hta : 0≤t-(3/4 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(13/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(47186633/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(47186633/16777216 : ℝ)=(17019593 : ℝ)*(t-(3/4 : ℝ))^0*((13/16 : ℝ)-t)^6 + (84400310 : ℝ)*(t-(3/4 : ℝ))^1*((13/16 : ℝ)-t)^5 + (167267015 : ℝ)*(t-(3/4 : ℝ))^2*((13/16 : ℝ)-t)^4 + (165597876 : ℝ)*(t-(3/4 : ℝ))^3*((13/16 : ℝ)-t)^3 + (81898135 : ℝ)*(t-(3/4 : ℝ))^4*((13/16 : ℝ)-t)^2 + (16186558 : ℝ)*(t-(3/4 : ℝ))^5*((13/16 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(47186633/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (47186633/16777216 : ℝ)-kernelVariationPolynomial t=(77353673 : ℝ)*(t-(3/4 : ℝ))^0*((13/16 : ℝ)-t)^6 + (481839286 : ℝ)*(t-(3/4 : ℝ))^1*((13/16 : ℝ)-t)^5 + (1248331975 : ℝ)*(t-(3/4 : ℝ))^2*((13/16 : ℝ)-t)^4 + (1721867444 : ℝ)*(t-(3/4 : ℝ))^3*((13/16 : ℝ)-t)^3 + (1333700855 : ℝ)*(t-(3/4 : ℝ))^4*((13/16 : ℝ)-t)^2 + (550053038 : ℝ)*(t-(3/4 : ℝ))^5*((13/16 : ℝ)-t)^1 + (94373266 : ℝ)*(t-(3/4 : ℝ))^6*((13/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_12 :
    (∫ t in (3/4 : ℝ)..(13/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(47186633/194400000 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (3/4 : ℝ) (13/16 : ℝ) (47186633/16777216 : ℝ) (1048576/759375 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_12 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 5 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_13 (t : ℝ) (ht : t ∈ Icc (13/16 : ℝ) (7/8 : ℝ)) :
    |kernelVariationPolynomial t|≤(973161/262144 : ℝ) := by
  have hta : 0≤t-(13/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(7/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(973161/262144 : ℝ) := by
    rw [show kernelVariationPolynomial t+(973161/262144 : ℝ)=(15095671 : ℝ)*(t-(13/16 : ℝ))^0*((7/8 : ℝ)-t)^6 + (74387468 : ℝ)*(t-(13/16 : ℝ))^1*((7/8 : ℝ)-t)^5 + (146467620 : ℝ)*(t-(13/16 : ℝ))^2*((7/8 : ℝ)-t)^4 + (144038304 : ℝ)*(t-(13/16 : ℝ))^3*((7/8 : ℝ)-t)^3 + (70745424 : ℝ)*(t-(13/16 : ℝ))^4*((7/8 : ℝ)-t)^2 + (13882944 : ℝ)*(t-(13/16 : ℝ))^5*((7/8 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(973161/262144 : ℝ)-kernelVariationPolynomial t := by
    rw [show (973161/262144 : ℝ)-kernelVariationPolynomial t=(109468937 : ℝ)*(t-(13/16 : ℝ))^0*((7/8 : ℝ)-t)^6 + (673000180 : ℝ)*(t-(13/16 : ℝ))^1*((7/8 : ℝ)-t)^5 + (1722001500 : ℝ)*(t-(13/16 : ℝ))^2*((7/8 : ℝ)-t)^4 + (2347253856 : ℝ)*(t-(13/16 : ℝ))^3*((7/8 : ℝ)-t)^3 + (1797723696 : ℝ)*(t-(13/16 : ℝ))^4*((7/8 : ℝ)-t)^2 + (733504704 : ℝ)*(t-(13/16 : ℝ))^5*((7/8 : ℝ)-t)^1 + (124564608 : ℝ)*(t-(13/16 : ℝ))^6*((7/8 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_13 :
    (∫ t in (13/16 : ℝ)..(7/8 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(144172/421875 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (13/16 : ℝ) (7/8 : ℝ) (973161/262144 : ℝ) (16777216/11390625 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_13 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 6 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_14 (t : ℝ) (ht : t ∈ Icc (7/8 : ℝ) (15/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(74724945/16777216 : ℝ) := by
  have hta : 0≤t-(7/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(15/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(74724945/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(74724945/16777216 : ℝ)=(12442641 : ℝ)*(t-(7/8 : ℝ))^0*((15/16 : ℝ)-t)^6 + (60772902 : ℝ)*(t-(7/8 : ℝ))^1*((15/16 : ℝ)-t)^5 + (118555599 : ℝ)*(t-(7/8 : ℝ))^2*((15/16 : ℝ)-t)^4 + (115460148 : ℝ)*(t-(7/8 : ℝ))^3*((15/16 : ℝ)-t)^3 + (56132067 : ℝ)*(t-(7/8 : ℝ))^4*((15/16 : ℝ)-t)^2 + (10897258 : ℝ)*(t-(7/8 : ℝ))^5*((15/16 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(74724945/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (74724945/16777216 : ℝ)-kernelVariationPolynomial t=(137007249 : ℝ)*(t-(7/8 : ℝ))^0*((15/16 : ℝ)-t)^6 + (835926438 : ℝ)*(t-(7/8 : ℝ))^1*((15/16 : ℝ)-t)^5 + (2123192751 : ℝ)*(t-(7/8 : ℝ))^2*((15/16 : ℝ)-t)^4 + (2873537652 : ℝ)*(t-(7/8 : ℝ))^3*((15/16 : ℝ)-t)^3 + (2185616283 : ℝ)*(t-(7/8 : ℝ))^4*((15/16 : ℝ)-t)^2 + (885802082 : ℝ)*(t-(7/8 : ℝ))^5*((15/16 : ℝ)-t)^1 + (149449890 : ℝ)*(t-(7/8 : ℝ))^6*((15/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_14 :
    (∫ t in (7/8 : ℝ)..(15/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(4981663/11390625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (7/8 : ℝ) (15/16 : ℝ) (74724945/16777216 : ℝ) (268435456/170859375 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_14 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 7 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_15 (t : ℝ) (ht : t ∈ Icc (15/16 : ℝ) (1 : ℝ)) :
    |kernelVariationPolynomial t|≤(5 : ℝ) := by
  have hta : 0≤t-(15/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(5 : ℝ) := by
    rw [show kernelVariationPolynomial t+(5 : ℝ)=(9161135 : ℝ)*(t-(15/16 : ℝ))^0*((1 : ℝ)-t)^6 + (44069552 : ℝ)*(t-(15/16 : ℝ))^1*((1 : ℝ)-t)^5 + (84576512 : ℝ)*(t-(15/16 : ℝ))^2*((1 : ℝ)-t)^4 + (80928768 : ℝ)*(t-(15/16 : ℝ))^3*((1 : ℝ)-t)^3 + (38600704 : ℝ)*(t-(15/16 : ℝ))^4*((1 : ℝ)-t)^2 + (7340032 : ℝ)*(t-(15/16 : ℝ))^5*((1 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(5 : ℝ)-kernelVariationPolynomial t := by
    rw [show (5 : ℝ)-kernelVariationPolynomial t=(158611025 : ℝ)*(t-(15/16 : ℝ))^0*((1 : ℝ)-t)^6 + (962563408 : ℝ)*(t-(15/16 : ℝ))^1*((1 : ℝ)-t)^5 + (2432005888 : ℝ)*(t-(15/16 : ℝ))^2*((1 : ℝ)-t)^4 + (3274514432 : ℝ)*(t-(15/16 : ℝ))^3*((1 : ℝ)-t)^3 + (2477981696 : ℝ)*(t-(15/16 : ℝ))^4*((1 : ℝ)-t)^2 + (999292928 : ℝ)*(t-(15/16 : ℝ))^5*((1 : ℝ)-t)^1 + (167772160 : ℝ)*(t-(15/16 : ℝ))^6*((1 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_15 :
    (∫ t in (15/16 : ℝ)..(1 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(268435456/512578125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (15/16 : ℝ) (1 : ℝ) (5 : ℝ) (4294967296/2562890625 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_15 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 8 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_16 (t : ℝ) (ht : t ∈ Icc (1 : ℝ) (17/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(89257905/16777216 : ℝ) := by
  have hta : 0≤t-(1 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(17/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(89257905/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(89257905/16777216 : ℝ)=(5371825 : ℝ)*(t-(1 : ℝ))^0*((17/16 : ℝ)-t)^6 + (24890918 : ℝ)*(t-(1 : ℝ))^1*((17/16 : ℝ)-t)^5 + (45777759 : ℝ)*(t-(1 : ℝ))^2*((17/16 : ℝ)-t)^4 + (41712084 : ℝ)*(t-(1 : ℝ))^3*((17/16 : ℝ)-t)^3 + (18795615 : ℝ)*(t-(1 : ℝ))^4*((17/16 : ℝ)-t)^2 + (3342198 : ℝ)*(t-(1 : ℝ))^5*((17/16 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(89257905/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (89257905/16777216 : ℝ)-kernelVariationPolynomial t=(173143985 : ℝ)*(t-(1 : ℝ))^0*((17/16 : ℝ)-t)^6 + (1046203942 : ℝ)*(t-(1 : ℝ))^1*((17/16 : ℝ)-t)^5 + (2631959391 : ℝ)*(t-(1 : ℝ))^2*((17/16 : ℝ)-t)^4 + (3528604116 : ℝ)*(t-(1 : ℝ))^3*((17/16 : ℝ)-t)^3 + (2658941535 : ℝ)*(t-(1 : ℝ))^4*((17/16 : ℝ)-t)^2 + (1067752662 : ℝ)*(t-(1 : ℝ))^5*((17/16 : ℝ)-t)^1 + (178515810 : ℝ)*(t-(1 : ℝ))^6*((17/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_16 :
    (∫ t in (1 : ℝ)..(17/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(507778304/854296875 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (1 : ℝ) (17/16 : ℝ) (89257905/16777216 : ℝ) (68719476736/38443359375 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_16 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 9 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_17 (t : ℝ) (ht : t ∈ Icc (17/16 : ℝ) (9/8 : ℝ)) :
    |kernelVariationPolynomial t|≤(5665185/1048576 : ℝ) := by
  have hta : 0≤t-(17/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(9/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(5665185/1048576 : ℝ) := by
    rw [show kernelVariationPolynomial t+(5665185/1048576 : ℝ)=(1385055 : ℝ)*(t-(17/16 : ℝ))^0*((9/8 : ℝ)-t)^6 + (4968132 : ℝ)*(t-(17/16 : ℝ))^1*((9/8 : ℝ)-t)^5 + (6149460 : ℝ)*(t-(17/16 : ℝ))^2*((9/8 : ℝ)-t)^4 + (2666016 : ℝ)*(t-(17/16 : ℝ))^3*((9/8 : ℝ)-t)^3 + (69280 : ℝ)*(t-(17/16 : ℝ))^5*((9/8 : ℝ)-t)^1 + (168912 : ℝ)*(t-(17/16 : ℝ))^6*((9/8 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(5665185/1048576 : ℝ)-kernelVariationPolynomial t := by
    rw [show (5665185/1048576 : ℝ)-kernelVariationPolynomial t=(179900865 : ℝ)*(t-(17/16 : ℝ))^0*((9/8 : ℝ)-t)^6 + (1082747388 : ℝ)*(t-(17/16 : ℝ))^1*((9/8 : ℝ)-t)^5 + (2713139340 : ℝ)*(t-(17/16 : ℝ))^2*((9/8 : ℝ)-t)^4 + (3623052384 : ℝ)*(t-(17/16 : ℝ))^3*((9/8 : ℝ)-t)^3 + (2719288800 : ℝ)*(t-(17/16 : ℝ))^4*((9/8 : ℝ)-t)^2 + (1087646240 : ℝ)*(t-(17/16 : ℝ))^5*((9/8 : ℝ)-t)^1 + (181117008 : ℝ)*(t-(17/16 : ℝ))^6*((9/8 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_17 :
    (∫ t in (17/16 : ℝ)..(9/8 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(8250523648/12814453125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (17/16 : ℝ) (9/8 : ℝ) (5665185/1048576 : ℝ) (1099511627776/576650390625 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_17 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 10 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_18 (t : ℝ) (ht : t ∈ Icc (9/8 : ℝ) (19/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(1413657/262144 : ℝ) := by
  have hta : 0≤t-(9/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(19/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(1413657/262144 : ℝ) := by
    rw [show kernelVariationPolynomial t+(1413657/262144 : ℝ)=(944192 : ℝ)*(t-(9/8 : ℝ))^1*((19/16 : ℝ)-t)^5 + (6908240 : ℝ)*(t-(9/8 : ℝ))^2*((19/16 : ℝ)-t)^4 + (18210464 : ℝ)*(t-(9/8 : ℝ))^3*((19/16 : ℝ)-t)^3 + (22616164 : ℝ)*(t-(9/8 : ℝ))^4*((19/16 : ℝ)-t)^2 + (13512748 : ℝ)*(t-(9/8 : ℝ))^5*((19/16 : ℝ)-t)^1 + (3142999 : ℝ)*(t-(9/8 : ℝ))^6*((19/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(1413657/262144 : ℝ)-kernelVariationPolynomial t := by
    rw [show (1413657/262144 : ℝ)-kernelVariationPolynomial t=(180948096 : ℝ)*(t-(9/8 : ℝ))^0*((19/16 : ℝ)-t)^6 + (1084744384 : ℝ)*(t-(9/8 : ℝ))^1*((19/16 : ℝ)-t)^5 + (2707313200 : ℝ)*(t-(9/8 : ℝ))^2*((19/16 : ℝ)-t)^4 + (3600751456 : ℝ)*(t-(9/8 : ℝ))^3*((19/16 : ℝ)-t)^3 + (2691605276 : ℝ)*(t-(9/8 : ℝ))^4*((19/16 : ℝ)-t)^2 + (1072175828 : ℝ)*(t-(9/8 : ℝ))^5*((19/16 : ℝ)-t)^1 + (177805097 : ℝ)*(t-(9/8 : ℝ))^6*((19/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_18 :
    (∫ t in (9/8 : ℝ)..(19/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(658811912192/961083984375 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (9/8 : ℝ) (19/16 : ℝ) (1413657/262144 : ℝ) (17592186044416/8649755859375 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_18 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 11 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_19 (t : ℝ) (ht : t ∈ Icc (19/16 : ℝ) (5/4 : ℝ)) :
    |kernelVariationPolynomial t|≤(87331049/16777216 : ℝ) := by
  have hta : 0≤t-(19/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(5/4 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(87331049/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(87331049/16777216 : ℝ)=(5345246 : ℝ)*(t-(19/16 : ℝ))^1*((5/4 : ℝ)-t)^5 + (28923639 : ℝ)*(t-(19/16 : ℝ))^2*((5/4 : ℝ)-t)^4 + (62228788 : ℝ)*(t-(19/16 : ℝ))^3*((5/4 : ℝ)-t)^3 + (66588327 : ℝ)*(t-(19/16 : ℝ))^4*((5/4 : ℝ)-t)^2 + (35458422 : ℝ)*(t-(19/16 : ℝ))^5*((5/4 : ℝ)-t)^1 + (7520489 : ℝ)*(t-(19/16 : ℝ))^6*((5/4 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(87331049/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (87331049/16777216 : ℝ)-kernelVariationPolynomial t=(174662098 : ℝ)*(t-(19/16 : ℝ))^0*((5/4 : ℝ)-t)^6 + (1042627342 : ℝ)*(t-(19/16 : ℝ))^1*((5/4 : ℝ)-t)^5 + (2591007831 : ℝ)*(t-(19/16 : ℝ))^2*((5/4 : ℝ)-t)^4 + (3431013172 : ℝ)*(t-(19/16 : ℝ))^3*((5/4 : ℝ)-t)^3 + (2553343143 : ℝ)*(t-(19/16 : ℝ))^4*((5/4 : ℝ)-t)^2 + (1012514166 : ℝ)*(t-(19/16 : ℝ))^5*((5/4 : ℝ)-t)^1 + (167141609 : ℝ)*(t-(19/16 : ℝ))^6*((5/4 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_19 :
    (∫ t in (19/16 : ℝ)..(5/4 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(91573242036224/129746337890625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (19/16 : ℝ) (5/4 : ℝ) (87331049/16777216 : ℝ) (281474976710656/129746337890625 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_19 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 12 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_20 (t : ℝ) (ht : t ∈ Icc (5/4 : ℝ) (21/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(19485/4096 : ℝ) := by
  have hta : 0≤t-(5/4 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(21/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(19485/4096 : ℝ) := by
    rw [show kernelVariationPolynomial t+(19485/4096 : ℝ)=(9664512 : ℝ)*(t-(5/4 : ℝ))^1*((21/16 : ℝ)-t)^5 + (50426112 : ℝ)*(t-(5/4 : ℝ))^2*((21/16 : ℝ)-t)^4 + (105009408 : ℝ)*(t-(5/4 : ℝ))^3*((21/16 : ℝ)-t)^3 + (109107024 : ℝ)*(t-(5/4 : ℝ))^4*((21/16 : ℝ)-t)^2 + (56567512 : ℝ)*(t-(5/4 : ℝ))^5*((21/16 : ℝ)-t)^1 + (11708295 : ℝ)*(t-(5/4 : ℝ))^6*((21/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(19485/4096 : ℝ)-kernelVariationPolynomial t := by
    rw [show (19485/4096 : ℝ)-kernelVariationPolynomial t=(159621120 : ℝ)*(t-(5/4 : ℝ))^0*((21/16 : ℝ)-t)^6 + (948062208 : ℝ)*(t-(5/4 : ℝ))^1*((21/16 : ℝ)-t)^5 + (2343890688 : ℝ)*(t-(5/4 : ℝ))^2*((21/16 : ℝ)-t)^4 + (3087412992 : ℝ)*(t-(5/4 : ℝ))^3*((21/16 : ℝ)-t)^3 + (2285209776 : ℝ)*(t-(5/4 : ℝ))^4*((21/16 : ℝ)-t)^2 + (901159208 : ℝ)*(t-(5/4 : ℝ))^5*((21/16 : ℝ)-t)^1 + (147912825 : ℝ)*(t-(5/4 : ℝ))^6*((21/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_20 :
    (∫ t in (5/4 : ℝ)..(21/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(29755533426688/43248779296875 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (5/4 : ℝ) (21/16 : ℝ) (19485/4096 : ℝ) (4503599627370496/1946195068359375 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_20 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 13 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_21 (t : ℝ) (ht : t ∈ Icc (21/16 : ℝ) (11/8 : ℝ)) :
    |kernelVariationPolynomial t|≤(68102265/16777216 : ℝ) := by
  have hta : 0≤t-(21/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(11/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(68102265/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(68102265/16777216 : ℝ)=(13682258 : ℝ)*(t-(21/16 : ℝ))^1*((11/8 : ℝ)-t)^5 + (70305179 : ℝ)*(t-(21/16 : ℝ))^2*((11/8 : ℝ)-t)^4 + (144307604 : ℝ)*(t-(21/16 : ℝ))^3*((11/8 : ℝ)-t)^3 + (147903655 : ℝ)*(t-(21/16 : ℝ))^4*((11/8 : ℝ)-t)^2 + (75693718 : ℝ)*(t-(21/16 : ℝ))^5*((11/8 : ℝ)-t)^1 + (15474745 : ℝ)*(t-(21/16 : ℝ))^6*((11/8 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(68102265/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (68102265/16777216 : ℝ)-kernelVariationPolynomial t=(136204530 : ℝ)*(t-(21/16 : ℝ))^0*((11/8 : ℝ)-t)^6 + (803544922 : ℝ)*(t-(21/16 : ℝ))^1*((11/8 : ℝ)-t)^5 + (1972762771 : ℝ)*(t-(21/16 : ℝ))^2*((11/8 : ℝ)-t)^4 + (2579782996 : ℝ)*(t-(21/16 : ℝ))^3*((11/8 : ℝ)-t)^3 + (1895164295 : ℝ)*(t-(21/16 : ℝ))^4*((11/8 : ℝ)-t)^2 + (741533462 : ℝ)*(t-(21/16 : ℝ))^5*((11/8 : ℝ)-t)^1 + (120729785 : ℝ)*(t-(21/16 : ℝ))^6*((11/8 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_21 :
    (∫ t in (21/16 : ℝ)..(11/8 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(1218737503993856/1946195068359375 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (21/16 : ℝ) (11/8 : ℝ) (68102265/16777216 : ℝ) (72057594037927936/29192926025390625 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_21 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 14 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_22 (t : ℝ) (ht : t ∈ Icc (11/8 : ℝ) (23/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(822305/262144 : ℝ) := by
  have hta : 0≤t-(11/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(23/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(822305/262144 : ℝ) := by
    rw [show kernelVariationPolynomial t+(822305/262144 : ℝ)=(17154752 : ℝ)*(t-(11/8 : ℝ))^1*((23/16 : ℝ)-t)^5 + (87330000 : ℝ)*(t-(11/8 : ℝ))^2*((23/16 : ℝ)-t)^4 + (177637216 : ℝ)*(t-(11/8 : ℝ))^3*((23/16 : ℝ)-t)^3 + (180467460 : ℝ)*(t-(11/8 : ℝ))^4*((23/16 : ℝ)-t)^2 + (91569300 : ℝ)*(t-(11/8 : ℝ))^5*((23/16 : ℝ)-t)^1 + (18563807 : ℝ)*(t-(11/8 : ℝ))^6*((23/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(822305/262144 : ℝ)-kernelVariationPolynomial t := by
    rw [show (822305/262144 : ℝ)-kernelVariationPolynomial t=(105255040 : ℝ)*(t-(11/8 : ℝ))^0*((23/16 : ℝ)-t)^6 + (614375488 : ℝ)*(t-(11/8 : ℝ))^1*((23/16 : ℝ)-t)^5 + (1491495600 : ℝ)*(t-(11/8 : ℝ))^2*((23/16 : ℝ)-t)^4 + (1927463584 : ℝ)*(t-(11/8 : ℝ))^3*((23/16 : ℝ)-t)^3 + (1398358140 : ℝ)*(t-(11/8 : ℝ))^4*((23/16 : ℝ)-t)^2 + (539960940 : ℝ)*(t-(11/8 : ℝ))^5*((23/16 : ℝ)-t)^1 + (86691233 : ℝ)*(t-(11/8 : ℝ))^6*((23/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_22 :
    (∫ t in (11/8 : ℝ)..(23/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(45206695453917184/87578778076171875 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (11/8 : ℝ) (23/16 : ℝ) (822305/262144 : ℝ) (1152921504606846976/437893890380859375 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_22 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 15 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_23 (t : ℝ) (ht : t ∈ Icc (23/16 : ℝ) (3/2 : ℝ)) :
    |kernelVariationPolynomial t|≤(34063713/16777216 : ℝ) := by
  have hta : 0≤t-(23/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(3/2 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(34063713/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(34063713/16777216 : ℝ)=(19813542 : ℝ)*(t-(23/16 : ℝ))^1*((3/2 : ℝ)-t)^5 + (100145775 : ℝ)*(t-(23/16 : ℝ))^2*((3/2 : ℝ)-t)^4 + (202263444 : ℝ)*(t-(23/16 : ℝ))^3*((3/2 : ℝ)-t)^3 + (204038319 : ℝ)*(t-(23/16 : ℝ))^4*((3/2 : ℝ)-t)^2 + (102801478 : ℝ)*(t-(23/16 : ℝ))^5*((3/2 : ℝ)-t)^1 + (20694369 : ℝ)*(t-(23/16 : ℝ))^6*((3/2 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(34063713/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (34063713/16777216 : ℝ)-kernelVariationPolynomial t=(68127426 : ℝ)*(t-(23/16 : ℝ))^0*((3/2 : ℝ)-t)^6 + (388951014 : ℝ)*(t-(23/16 : ℝ))^1*((3/2 : ℝ)-t)^5 + (921765615 : ℝ)*(t-(23/16 : ℝ))^2*((3/2 : ℝ)-t)^4 + (1160285076 : ℝ)*(t-(23/16 : ℝ))^3*((3/2 : ℝ)-t)^3 + (817873071 : ℝ)*(t-(23/16 : ℝ))^4*((3/2 : ℝ)-t)^2 + (305963078 : ℝ)*(t-(23/16 : ℝ))^5*((3/2 : ℝ)-t)^1 + (47433057 : ℝ)*(t-(23/16 : ℝ))^6*((3/2 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_23 :
    (∫ t in (23/16 : ℝ)..(3/2 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(86697797520195584/243274383544921875 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (23/16 : ℝ) (3/2 : ℝ) (34063713/16777216 : ℝ) (18446744073709551616/6568408355712890625 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_23 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 16 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_24 (t : ℝ) (ht : t ∈ Icc (3/2 : ℝ) (25/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(51/64 : ℝ) := by
  have hta : 0≤t-(3/2 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(25/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(51/64 : ℝ) := by
    rw [show kernelVariationPolynomial t+(51/64 : ℝ)=(21364736 : ℝ)*(t-(3/2 : ℝ))^1*((25/16 : ℝ)-t)^5 + (107270144 : ℝ)*(t-(3/2 : ℝ))^2*((25/16 : ℝ)-t)^4 + (215195648 : ℝ)*(t-(3/2 : ℝ))^3*((25/16 : ℝ)-t)^3 + (215599552 : ℝ)*(t-(3/2 : ℝ))^4*((25/16 : ℝ)-t)^2 + (107868832 : ℝ)*(t-(3/2 : ℝ))^5*((25/16 : ℝ)-t)^1 + (21559519 : ℝ)*(t-(3/2 : ℝ))^6*((25/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(51/64 : ℝ)-kernelVariationPolynomial t := by
    rw [show (51/64 : ℝ)-kernelVariationPolynomial t=(26738688 : ℝ)*(t-(3/2 : ℝ))^0*((25/16 : ℝ)-t)^6 + (139067392 : ℝ)*(t-(3/2 : ℝ))^1*((25/16 : ℝ)-t)^5 + (293810176 : ℝ)*(t-(3/2 : ℝ))^2*((25/16 : ℝ)-t)^4 + (319578112 : ℝ)*(t-(3/2 : ℝ))^3*((25/16 : ℝ)-t)^3 + (185480768 : ℝ)*(t-(3/2 : ℝ))^4*((25/16 : ℝ)-t)^2 + (52563296 : ℝ)*(t-(3/2 : ℝ))^5*((25/16 : ℝ)-t)^1 + (5179169 : ℝ)*(t-(3/2 : ℝ))^6*((25/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_24 :
    (∫ t in (3/2 : ℝ)..(25/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(4899916394579099648/32842041778564453125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (3/2 : ℝ) (25/16 : ℝ) (51/64 : ℝ) (295147905179352825856/98526125335693359375 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_24 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 17 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_25 (t : ℝ) (ht : t ∈ Icc (25/16 : ℝ) (13/8 : ℝ)) :
    |kernelVariationPolynomial t|≤(453375/262144 : ℝ) := by
  have hta : 0≤t-(25/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(13/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(453375/262144 : ℝ) := by
    rw [show kernelVariationPolynomial t+(453375/262144 : ℝ)=(37206175 : ℝ)*(t-(25/16 : ℝ))^0*((13/8 : ℝ)-t)^6 + (244725332 : ℝ)*(t-(25/16 : ℝ))^1*((13/8 : ℝ)-t)^5 + (665182212 : ℝ)*(t-(25/16 : ℝ))^2*((13/8 : ℝ)-t)^4 + (957303648 : ℝ)*(t-(25/16 : ℝ))^3*((13/8 : ℝ)-t)^3 + (769963344 : ℝ)*(t-(25/16 : ℝ))^4*((13/8 : ℝ)-t)^2 + (328354752 : ℝ)*(t-(25/16 : ℝ))^5*((13/8 : ℝ)-t)^1 + (58032000 : ℝ)*(t-(25/16 : ℝ))^6*((13/8 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(453375/262144 : ℝ)-kernelVariationPolynomial t := by
    rw [show (453375/262144 : ℝ)-kernelVariationPolynomial t=(20825825 : ℝ)*(t-(25/16 : ℝ))^0*((13/8 : ℝ)-t)^6 + (103466668 : ℝ)*(t-(25/16 : ℝ))^1*((13/8 : ℝ)-t)^5 + (205297788 : ℝ)*(t-(25/16 : ℝ))^2*((13/8 : ℝ)-t)^4 + (203336352 : ℝ)*(t-(25/16 : ℝ))^3*((13/8 : ℝ)-t)^3 + (100516656 : ℝ)*(t-(25/16 : ℝ))^4*((13/8 : ℝ)-t)^2 + (19837248 : ℝ)*(t-(25/16 : ℝ))^5*((13/8 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_25 :
    (∫ t in (25/16 : ℝ)..(13/8 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(453737662457577472/1313681671142578125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (25/16 : ℝ) (13/8 : ℝ) (453375/262144 : ℝ) (4722366482869645213696/1477891880035400390625 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_25 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 18 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_26 (t : ℝ) (ht : t ∈ Icc (13/8 : ℝ) (27/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(47148615/16777216 : ℝ) := by
  have hta : 0≤t-(13/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(27/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(47148615/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(47148615/16777216 : ℝ)=(76164615 : ℝ)*(t-(13/8 : ℝ))^0*((27/16 : ℝ)-t)^6 + (476824938 : ℝ)*(t-(13/8 : ℝ))^1*((27/16 : ℝ)-t)^5 + (1240325049 : ℝ)*(t-(13/8 : ℝ))^2*((27/16 : ℝ)-t)^4 + (1715985324 : ℝ)*(t-(13/8 : ℝ))^3*((27/16 : ℝ)-t)^3 + (1331769645 : ℝ)*(t-(13/8 : ℝ))^4*((27/16 : ℝ)-t)^2 + (549746278 : ℝ)*(t-(13/8 : ℝ))^5*((27/16 : ℝ)-t)^1 + (94297230 : ℝ)*(t-(13/8 : ℝ))^6*((27/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(47148615/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (47148615/16777216 : ℝ)-kernelVariationPolynomial t=(18132615 : ℝ)*(t-(13/8 : ℝ))^0*((27/16 : ℝ)-t)^6 + (88958442 : ℝ)*(t-(13/8 : ℝ))^1*((27/16 : ℝ)-t)^5 + (174133401 : ℝ)*(t-(13/8 : ℝ))^2*((27/16 : ℝ)-t)^4 + (169959276 : ℝ)*(t-(13/8 : ℝ))^3*((27/16 : ℝ)-t)^3 + (82688805 : ℝ)*(t-(13/8 : ℝ))^4*((27/16 : ℝ)-t)^2 + (16037102 : ℝ)*(t-(13/8 : ℝ))^5*((27/16 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_26 :
    (∫ t in (13/8 : ℝ)..(27/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(98304854141219897344/164210208892822265625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (13/8 : ℝ) (27/16 : ℝ) (47148615/16777216 : ℝ) (75557863725914323419136/22168378200531005859375 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_26 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 19 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_27 (t : ℝ) (ht : t ∈ Icc (27/16 : ℝ) (7/4 : ℝ)) :
    |kernelVariationPolynomial t|≤(14707/4096 : ℝ) := by
  have hta : 0≤t-(27/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(7/4 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(14707/4096 : ℝ) := by
    rw [show kernelVariationPolynomial t+(14707/4096 : ℝ)=(107388487 : ℝ)*(t-(27/16 : ℝ))^0*((7/4 : ℝ)-t)^6 + (660368024 : ℝ)*(t-(27/16 : ℝ))^1*((7/4 : ℝ)-t)^5 + (1688509520 : ℝ)*(t-(27/16 : ℝ))^2*((7/4 : ℝ)-t)^4 + (2297702656 : ℝ)*(t-(27/16 : ℝ))^3*((7/4 : ℝ)-t)^3 + (1754886400 : ℝ)*(t-(27/16 : ℝ))^4*((7/4 : ℝ)-t)^2 + (713193472 : ℝ)*(t-(27/16 : ℝ))^5*((7/4 : ℝ)-t)^1 + (120479744 : ℝ)*(t-(27/16 : ℝ))^6*((7/4 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(14707/4096 : ℝ)-kernelVariationPolynomial t := by
    rw [show (14707/4096 : ℝ)-kernelVariationPolynomial t=(13091257 : ℝ)*(t-(27/16 : ℝ))^0*((7/4 : ℝ)-t)^6 + (62510440 : ℝ)*(t-(27/16 : ℝ))^1*((7/4 : ℝ)-t)^5 + (118686640 : ℝ)*(t-(27/16 : ℝ))^2*((7/4 : ℝ)-t)^4 + (111892224 : ℝ)*(t-(27/16 : ℝ))^3*((7/4 : ℝ)-t)^3 + (52309760 : ℝ)*(t-(27/16 : ℝ))^4*((7/4 : ℝ)-t)^2 + (9684992 : ℝ)*(t-(27/16 : ℝ))^5*((7/4 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_27 :
    (∫ t in (27/16 : ℝ)..(7/4 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(271296265092046375616512/332525673007965087890625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (27/16 : ℝ) (7/4 : ℝ) (14707/4096 : ℝ) (1208925819614629174706176/332525673007965087890625 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_27 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 20 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_28 (t : ℝ) (ht : t ∈ Icc (7/4 : ℝ) (29/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(65524311/16777216 : ℝ) := by
  have hta : 0≤t-(7/4 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(29/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(65524311/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(65524311/16777216 : ℝ)=(125764183 : ℝ)*(t-(7/4 : ℝ))^0*((29/16 : ℝ)-t)^6 + (764270090 : ℝ)*(t-(7/4 : ℝ))^1*((29/16 : ℝ)-t)^5 + (1931002905 : ℝ)*(t-(7/4 : ℝ))^2*((29/16 : ℝ)-t)^4 + (2596097484 : ℝ)*(t-(7/4 : ℝ))^3*((29/16 : ℝ)-t)^3 + (1958494569 : ℝ)*(t-(7/4 : ℝ))^4*((29/16 : ℝ)-t)^2 + (785942706 : ℝ)*(t-(7/4 : ℝ))^5*((29/16 : ℝ)-t)^1 + (131048622 : ℝ)*(t-(7/4 : ℝ))^6*((29/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(65524311/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (65524311/16777216 : ℝ)-kernelVariationPolynomial t=(5284439 : ℝ)*(t-(7/4 : ℝ))^0*((29/16 : ℝ)-t)^6 + (22021642 : ℝ)*(t-(7/4 : ℝ))^1*((29/16 : ℝ)-t)^5 + (34726425 : ℝ)*(t-(7/4 : ℝ))^2*((29/16 : ℝ)-t)^4 + (24874956 : ℝ)*(t-(7/4 : ℝ))^3*((29/16 : ℝ)-t)^3 + (7234761 : ℝ)*(t-(7/4 : ℝ))^4*((29/16 : ℝ)-t)^2 + (349026 : ℝ)*(t-(7/4 : ℝ))^5*((29/16 : ℝ)-t)^1 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_28 :
    (∫ t in (7/4 : ℝ)..(29/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(524613800183659541561344/554209455013275146484375 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (7/4 : ℝ) (29/16 : ℝ) (65524311/16777216 : ℝ) (19342813113834066795298816/4987885095119476318359375 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_28 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 21 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_29 (t : ℝ) (ht : t ∈ Icc (29/16 : ℝ) (15/8 : ℝ)) :
    |kernelVariationPolynomial t|≤(32791241/8388608 : ℝ) := by
  have hta : 0≤t-(29/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(15/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(32791241/8388608 : ℝ) := by
    rw [show kernelVariationPolynomial t+(32791241/8388608 : ℝ)=(131106793 : ℝ)*(t-(29/16 : ℝ))^0*((15/8 : ℝ)-t)^6 + (786989784 : ℝ)*(t-(29/16 : ℝ))^1*((15/8 : ℝ)-t)^5 + (1962857394 : ℝ)*(t-(29/16 : ℝ))^2*((15/8 : ℝ)-t)^4 + (2603093768 : ℝ)*(t-(29/16 : ℝ))^3*((15/8 : ℝ)-t)^3 + (1935413022 : ℝ)*(t-(29/16 : ℝ))^4*((15/8 : ℝ)-t)^2 + (764665900 : ℝ)*(t-(29/16 : ℝ))^5*((15/8 : ℝ)-t)^1 + (125372242 : ℝ)*(t-(29/16 : ℝ))^6*((15/8 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(32791241/8388608 : ℝ)-kernelVariationPolynomial t := by
    rw [show (32791241/8388608 : ℝ)-kernelVariationPolynomial t=(58171 : ℝ)*(t-(29/16 : ℝ))^0*((15/8 : ℝ)-t)^6 + (4617066 : ℝ)*(t-(29/16 : ℝ))^2*((15/8 : ℝ)-t)^4 + (20205512 : ℝ)*(t-(29/16 : ℝ))^3*((15/8 : ℝ)-t)^3 + (32061438 : ℝ)*(t-(29/16 : ℝ))^4*((15/8 : ℝ)-t)^2 + (22323884 : ℝ)*(t-(29/16 : ℝ))^5*((15/8 : ℝ)-t)^1 + (5792722 : ℝ)*(t-(29/16 : ℝ))^6*((15/8 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_29 :
    (∫ t in (29/16 : ℝ)..(15/8 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(75611453823291458880274432/74818276426792144775390625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (29/16 : ℝ) (15/8 : ℝ) (32791241/8388608 : ℝ) (309485009821345068724781056/74818276426792144775390625 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_29 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 22 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_30 (t : ℝ) (ht : t ∈ Icc (15/8 : ℝ) (31/16 : ℝ)) :
    |kernelVariationPolynomial t|≤(934215/262144 : ℝ) := by
  have hta : 0≤t-(15/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(31/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(934215/262144 : ℝ) := by
    rw [show kernelVariationPolynomial t+(934215/262144 : ℝ)=(119579520 : ℝ)*(t-(15/8 : ℝ))^0*((31/16 : ℝ)-t)^6 + (705044672 : ℝ)*(t-(15/8 : ℝ))^1*((31/16 : ℝ)-t)^5 + (1724197712 : ℝ)*(t-(15/8 : ℝ))^2*((31/16 : ℝ)-t)^4 + (2237278688 : ℝ)*(t-(15/8 : ℝ))^3*((31/16 : ℝ)-t)^3 + (1623382564 : ℝ)*(t-(15/8 : ℝ))^4*((31/16 : ℝ)-t)^2 + (623973412 : ℝ)*(t-(15/8 : ℝ))^5*((31/16 : ℝ)-t)^1 + (99136975 : ℝ)*(t-(15/8 : ℝ))^6*((31/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(934215/262144 : ℝ)-kernelVariationPolynomial t := by
    rw [show (934215/262144 : ℝ)-kernelVariationPolynomial t=(12432448 : ℝ)*(t-(15/8 : ℝ))^1*((31/16 : ℝ)-t)^5 + (69495088 : ℝ)*(t-(15/8 : ℝ))^2*((31/16 : ℝ)-t)^4 + (154311712 : ℝ)*(t-(15/8 : ℝ))^3*((31/16 : ℝ)-t)^3 + (170310236 : ℝ)*(t-(15/8 : ℝ))^4*((31/16 : ℝ)-t)^2 + (93503708 : ℝ)*(t-(15/8 : ℝ))^5*((31/16 : ℝ)-t)^1 + (20442545 : ℝ)*(t-(15/8 : ℝ))^6*((31/16 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_30 :
    (∫ t in (15/8 : ℝ)..(31/16 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(73528426729901093388550144/74818276426792144775390625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (15/8 : ℝ) (31/16 : ℝ) (934215/262144 : ℝ) (4951760157141521099596496896/1122274146401882171630859375 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_30 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 23 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_mesh_31 (t : ℝ) (ht : t ∈ Icc (31/16 : ℝ) (2 : ℝ)) :
    |kernelVariationPolynomial t|≤(39347215/16777216 : ℝ) := by
  have hta : 0≤t-(31/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(2 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelVariationPolynomial t+(39347215/16777216 : ℝ) := by
    rw [show kernelVariationPolynomial t+(39347215/16777216 : ℝ)=(78694430 : ℝ)*(t-(31/16 : ℝ))^0*((2 : ℝ)-t)^6 + (443015018 : ℝ)*(t-(31/16 : ℝ))^1*((2 : ℝ)-t)^5 + (1025228769 : ℝ)*(t-(31/16 : ℝ))^2*((2 : ℝ)-t)^4 + (1243910444 : ℝ)*(t-(31/16 : ℝ))^3*((2 : ℝ)-t)^3 + (830069985 : ℝ)*(t-(31/16 : ℝ))^4*((2 : ℝ)-t)^2 + (286414938 : ℝ)*(t-(31/16 : ℝ))^5*((2 : ℝ)-t)^1 + (39347215 : ℝ)*(t-(31/16 : ℝ))^6*((2 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  have hhigh : 0≤(39347215/16777216 : ℝ)-kernelVariationPolynomial t := by
    rw [show (39347215/16777216 : ℝ)-kernelVariationPolynomial t=(29151562 : ℝ)*(t-(31/16 : ℝ))^1*((2 : ℝ)-t)^5 + (155187681 : ℝ)*(t-(31/16 : ℝ))^2*((2 : ℝ)-t)^4 + (329978156 : ℝ)*(t-(31/16 : ℝ))^3*((2 : ℝ)-t)^3 + (350346465 : ℝ)*(t-(31/16 : ℝ))^4*((2 : ℝ)-t)^2 + (185751642 : ℝ)*(t-(31/16 : ℝ))^5*((2 : ℝ)-t)^1 + (39347215 : ℝ)*(t-(31/16 : ℝ))^6*((2 : ℝ)-t)^0 by unfold kernelVariationPolynomial; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_variation_interval_31 :
    (∫ t in (31/16 : ℝ)..(2 : ℝ),|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(2322649616378321839962718208/3366822439205646514892578125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelVariationPolynomial (by unfold kernelVariationPolynomial; fun_prop)
    (31/16 : ℝ) (2 : ℝ) (39347215/16777216 : ℝ) (79228162514264337593543950336/16834112196028232574462890625 : ℝ) (by norm_num) (by norm_num)
    kernel_variation_mesh_31 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 24 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_variation_whole_interval :
    (∫ t in (0 : ℝ)..2,|kernelVariationPolynomial t| * Real.exp (t-1/2))≤(15 : ℝ) := by
  have hc : Continuous (fun t => |kernelVariationPolynomial t| * Real.exp (t-1/2)) := by unfold kernelVariationPolynomial; fun_prop
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := fun j : ℕ => (j : ℝ)/16) (n := 32)
    (fun k hk => hc.intervalIntegrable ((k : ℝ)/16) ((k+1 : ℕ)/16 : ℝ))
  norm_num only [Nat.cast_zero,zero_div,Nat.cast_ofNat] at hsum
  rw [← hsum]
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.cast_add,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  have h0 := kernel_variation_interval_0
  have h1 := kernel_variation_interval_1
  have h2 := kernel_variation_interval_2
  have h3 := kernel_variation_interval_3
  have h4 := kernel_variation_interval_4
  have h5 := kernel_variation_interval_5
  have h6 := kernel_variation_interval_6
  have h7 := kernel_variation_interval_7
  have h8 := kernel_variation_interval_8
  have h9 := kernel_variation_interval_9
  have h10 := kernel_variation_interval_10
  have h11 := kernel_variation_interval_11
  have h12 := kernel_variation_interval_12
  have h13 := kernel_variation_interval_13
  have h14 := kernel_variation_interval_14
  have h15 := kernel_variation_interval_15
  have h16 := kernel_variation_interval_16
  have h17 := kernel_variation_interval_17
  have h18 := kernel_variation_interval_18
  have h19 := kernel_variation_interval_19
  have h20 := kernel_variation_interval_20
  have h21 := kernel_variation_interval_21
  have h22 := kernel_variation_interval_22
  have h23 := kernel_variation_interval_23
  have h24 := kernel_variation_interval_24
  have h25 := kernel_variation_interval_25
  have h26 := kernel_variation_interval_26
  have h27 := kernel_variation_interval_27
  have h28 := kernel_variation_interval_28
  have h29 := kernel_variation_interval_29
  have h30 := kernel_variation_interval_30
  have h31 := kernel_variation_interval_31
  norm_num at *
  linarith

lemma kernel_mass_whole_interval : (∫ t in (0 : ℝ)..2,|kernelMassPolynomial t| * Real.exp (t-1/2))≤5/2 := by
  exact kernel_mass_whole_interval_exact

end Helfgott
end

theorem solution : Helfgott.KernelPolynomialMoments := by
  exact ⟨Helfgott.kernel_mass_whole_interval,Helfgott.kernel_variation_whole_interval⟩

#print axioms solution
