-- Prove2me | solution 1 for Helfgott.actual_kernel_fourth_polynomial_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T11:08:49.522984+00:00
-- url     : https://prove2.me/submissions/e6ee8cf2-b9b8-46e6-868d-308154bac296

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 6000
open MeasureTheory Set Finset
namespace Helfgott
noncomputable def logRawPoly4 (t : ℝ) : ℝ :=
  (128 : ℝ) + (-452 : ℝ)*t^1 + (-124 : ℝ)*t^2 + (537 : ℝ)*t^3 + (27 : ℝ)*t^4 + (-97 : ℝ)*t^5 + (-20 : ℝ)*t^6 + (-1 : ℝ)*t^7

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

noncomputable def kernelFourthDensityPolynomial (t : ℝ) : ℝ := t*logRawPoly4 t
lemma kernel_fourth_mesh_0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(26681691583/4294967296 : ℝ) := by
  have hta : 0≤t-(0 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(26681691583/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(26681691583/4294967296 : ℝ)=(26681691583 : ℝ)*(t-(0 : ℝ))^0*((1/16 : ℝ)-t)^8 + (247813271032 : ℝ)*(t-(0 : ℝ))^1*((1/16 : ℝ)-t)^7 + (980022231268 : ℝ)*(t-(0 : ℝ))^2*((1/16 : ℝ)-t)^6 + (2170099401160 : ℝ)*(t-(0 : ℝ))^3*((1/16 : ℝ)-t)^5 + (2955944804922 : ℝ)*(t-(0 : ℝ))^4*((1/16 : ℝ)-t)^4 + (2543940186568 : ℝ)*(t-(0 : ℝ))^5*((1/16 : ℝ)-t)^3 + (1353803575268 : ℝ)*(t-(0 : ℝ))^6*((1/16 : ℝ)-t)^2 + (407962827448 : ℝ)*(t-(0 : ℝ))^7*((1/16 : ℝ)-t)^1 + (53363383166 : ℝ)*(t-(0 : ℝ))^8*((1/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(26681691583/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (26681691583/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(26681691583 : ℝ)*(t-(0 : ℝ))^0*((1/16 : ℝ)-t)^8 + (179093794296 : ℝ)*(t-(0 : ℝ))^1*((1/16 : ℝ)-t)^7 + (514152497380 : ℝ)*(t-(0 : ℝ))^2*((1/16 : ℝ)-t)^6 + (818250056136 : ℝ)*(t-(0 : ℝ))^3*((1/16 : ℝ)-t)^5 + (779492016698 : ℝ)*(t-(0 : ℝ))^4*((1/16 : ℝ)-t)^4 + (444409270728 : ℝ)*(t-(0 : ℝ))^5*((1/16 : ℝ)-t)^3 + (140371153380 : ℝ)*(t-(0 : ℝ))^6*((1/16 : ℝ)-t)^2 + (18944237880 : ℝ)*(t-(0 : ℝ))^7*((1/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_0 :
    (∫ t in (0 : ℝ)..(1/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(26681691583/68719476736 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (0 : ℝ) (1/16 : ℝ) (26681691583/4294967296 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_0 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_1 (t : ℝ) (ht : t ∈ Icc (1/16 : ℝ) (1/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(148090143/16777216 : ℝ) := by
  have hta : 0≤t-(1/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(148090143/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(148090143/16777216 : ℝ)=(64592768191 : ℝ)*(t-(1/16 : ℝ))^0*((1/8 : ℝ)-t)^8 + (535686383408 : ℝ)*(t-(1/16 : ℝ))^1*((1/8 : ℝ)-t)^7 + (1933445686288 : ℝ)*(t-(1/16 : ℝ))^2*((1/8 : ℝ)-t)^6 + (3968466430784 : ℝ)*(t-(1/16 : ℝ))^3*((1/8 : ℝ)-t)^5 + (5068211867552 : ℝ)*(t-(1/16 : ℝ))^4*((1/8 : ℝ)-t)^4 + (4125268442368 : ℝ)*(t-(1/16 : ℝ))^5*((1/8 : ℝ)-t)^3 + (2090329650432 : ℝ)*(t-(1/16 : ℝ))^6*((1/8 : ℝ)-t)^2 + (602980869120 : ℝ)*(t-(1/16 : ℝ))^7*((1/8 : ℝ)-t)^1 + (75822153216 : ℝ)*(t-(1/16 : ℝ))^8*((1/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(148090143/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (148090143/16777216 : ℝ)-kernelFourthDensityPolynomial t=(11229385025 : ℝ)*(t-(1/16 : ℝ))^0*((1/8 : ℝ)-t)^8 + (70890842320 : ℝ)*(t-(1/16 : ℝ))^1*((1/8 : ℝ)-t)^7 + (189574603760 : ℝ)*(t-(1/16 : ℝ))^2*((1/8 : ℝ)-t)^6 + (277574149312 : ℝ)*(t-(1/16 : ℝ))^3*((1/8 : ℝ)-t)^5 + (239338857568 : ℝ)*(t-(1/16 : ℝ))^4*((1/8 : ℝ)-t)^4 + (120772137728 : ℝ)*(t-(1/16 : ℝ))^5*((1/8 : ℝ)-t)^3 + (32690639616 : ℝ)*(t-(1/16 : ℝ))^6*((1/8 : ℝ)-t)^2 + (3596356608 : ℝ)*(t-(1/16 : ℝ))^7*((1/8 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_1 :
    (∫ t in (1/16 : ℝ)..(1/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(148090143/268435456 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (1/16 : ℝ) (1/8 : ℝ) (148090143/16777216 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_1 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_2 (t : ℝ) (ht : t ∈ Icc (1/8 : ℝ) (3/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(4215501945/469762048 : ℝ) := by
  have hta : 0≤t-(1/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(3/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(4215501945/469762048 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(4215501945/469762048 : ℝ)=(535169660736/7 : ℝ)*(t-(1/8 : ℝ))^0*((3/16 : ℝ)-t)^8 + (4306531782144/7 : ℝ)*(t-(1/8 : ℝ))^1*((3/16 : ℝ)-t)^7 + (2158336995840 : ℝ)*(t-(1/8 : ℝ))^2*((3/16 : ℝ)-t)^6 + (4311935703296 : ℝ)*(t-(1/8 : ℝ))^3*((3/16 : ℝ)-t)^5 + (5365620600352 : ℝ)*(t-(1/8 : ℝ))^4*((3/16 : ℝ)-t)^4 + (4258563445696 : ℝ)*(t-(1/8 : ℝ))^5*((3/16 : ℝ)-t)^3 + (2105185504400 : ℝ)*(t-(1/8 : ℝ))^6*((3/16 : ℝ)-t)^2 + (4148180530288/7 : ℝ)*(t-(1/8 : ℝ))^7*((3/16 : ℝ)-t)^1 + (509034990489/7 : ℝ)*(t-(1/8 : ℝ))^8*((3/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(4215501945/469762048 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (4215501945/469762048 : ℝ)-kernelFourthDensityPolynomial t=(4414588224/7 : ℝ)*(t-(1/8 : ℝ))^0*((3/16 : ℝ)-t)^8 + (10142209536/7 : ℝ)*(t-(1/8 : ℝ))^1*((3/16 : ℝ)-t)^7 + (4738288384 : ℝ)*(t-(1/8 : ℝ))^3*((3/16 : ℝ)-t)^5 + (30221889248 : ℝ)*(t-(1/8 : ℝ))^4*((3/16 : ℝ)-t)^4 + (58110545984 : ℝ)*(t-(1/8 : ℝ))^5*((3/16 : ℝ)-t)^3 + (53151491440 : ℝ)*(t-(1/8 : ℝ))^6*((3/16 : ℝ)-t)^2 + (168493461392/7 : ℝ)*(t-(1/8 : ℝ))^7*((3/16 : ℝ)-t)^1 + (30549258471/7 : ℝ)*(t-(1/8 : ℝ))^8*((3/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_2 :
    (∫ t in (1/8 : ℝ)..(3/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(4215501945/7516192768 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (1/8 : ℝ) (3/16 : ℝ) (4215501945/469762048 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_2 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_3 (t : ℝ) (ht : t ∈ Icc (3/16 : ℝ) (1/4 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(34177552287/4294967296 : ℝ) := by
  have hta : 0≤t-(3/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1/4 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(34177552287/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(34177552287/4294967296 : ℝ)=(68355104574 : ℝ)*(t-(3/16 : ℝ))^0*((1/4 : ℝ)-t)^8 + (535997892824 : ℝ)*(t-(3/16 : ℝ))^1*((1/4 : ℝ)-t)^7 + (1831187257764 : ℝ)*(t-(3/16 : ℝ))^2*((1/4 : ℝ)-t)^6 + (3559341567176 : ℝ)*(t-(3/16 : ℝ))^3*((1/4 : ℝ)-t)^5 + (4304001089402 : ℝ)*(t-(3/16 : ℝ))^4*((1/4 : ℝ)-t)^4 + (3314293050056 : ℝ)*(t-(3/16 : ℝ))^5*((1/4 : ℝ)-t)^3 + (1586492208484 : ℝ)*(t-(3/16 : ℝ))^6*((1/4 : ℝ)-t)^2 + (431380921592 : ℝ)*(t-(3/16 : ℝ))^7*((1/4 : ℝ)-t)^1 + (50977771423 : ℝ)*(t-(3/16 : ℝ))^8*((1/4 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(34177552287/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (34177552287/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(10842943768 : ℝ)*(t-(3/16 : ℝ))^1*((1/4 : ℝ)-t)^7 + (82755670308 : ℝ)*(t-(3/16 : ℝ))^2*((1/4 : ℝ)-t)^6 + (268544288968 : ℝ)*(t-(3/16 : ℝ))^3*((1/4 : ℝ)-t)^5 + (480856230778 : ℝ)*(t-(3/16 : ℝ))^4*((1/4 : ℝ)-t)^4 + (513592806088 : ℝ)*(t-(3/16 : ℝ))^5*((1/4 : ℝ)-t)^3 + (327450719588 : ℝ)*(t-(3/16 : ℝ))^6*((1/4 : ℝ)-t)^2 + (115459915000 : ℝ)*(t-(3/16 : ℝ))^7*((1/4 : ℝ)-t)^1 + (17377333151 : ℝ)*(t-(3/16 : ℝ))^8*((1/4 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_3 :
    (∫ t in (3/16 : ℝ)..(1/4 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(34177552287/68719476736 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (3/16 : ℝ) (1/4 : ℝ) (34177552287/4294967296 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_3 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_4 (t : ℝ) (ht : t ∈ Icc (1/4 : ℝ) (5/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(256351/65536 : ℝ) := by
  have hta : 0≤t-(1/4 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(5/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(256351/65536 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(256351/65536 : ℝ)=(33600438272 : ℝ)*(t-(1/4 : ℝ))^0*((5/16 : ℝ)-t)^8 + (245244755968 : ℝ)*(t-(1/4 : ℝ))^1*((5/16 : ℝ)-t)^7 + (770104377344 : ℝ)*(t-(1/4 : ℝ))^2*((5/16 : ℝ)-t)^6 + (1352526979072 : ℝ)*(t-(1/4 : ℝ))^3*((5/16 : ℝ)-t)^5 + (1442635725312 : ℝ)*(t-(1/4 : ℝ))^4*((5/16 : ℝ)-t)^4 + (945418145280 : ℝ)*(t-(1/4 : ℝ))^5*((5/16 : ℝ)-t)^3 + (363471784000 : ℝ)*(t-(1/4 : ℝ))^6*((5/16 : ℝ)-t)^2 + (71313616160 : ℝ)*(t-(1/4 : ℝ))^7*((5/16 : ℝ)-t)^1 + (4691171551 : ℝ)*(t-(1/4 : ℝ))^8*((5/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(256351/65536 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (256351/65536 : ℝ)-kernelFourthDensityPolynomial t=(23558750208 : ℝ)*(t-(1/4 : ℝ))^1*((5/16 : ℝ)-t)^7 + (170707894272 : ℝ)*(t-(1/4 : ℝ))^2*((5/16 : ℝ)-t)^6 + (529097564160 : ℝ)*(t-(1/4 : ℝ))^3*((5/16 : ℝ)-t)^5 + (909394953728 : ℝ)*(t-(1/4 : ℝ))^4*((5/16 : ℝ)-t)^4 + (936206397952 : ℝ)*(t-(1/4 : ℝ))^5*((5/16 : ℝ)-t)^3 + (577340487616 : ℝ)*(t-(1/4 : ℝ))^6*((5/16 : ℝ)-t)^2 + (197489890016 : ℝ)*(t-(1/4 : ℝ))^7*((5/16 : ℝ)-t)^1 + (28909266721 : ℝ)*(t-(1/4 : ℝ))^8*((5/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_4 :
    (∫ t in (1/4 : ℝ)..(5/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(256351/1048576 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (1/4 : ℝ) (5/16 : ℝ) (256351/65536 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_4 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_5 (t : ℝ) (ht : t ∈ Icc (5/16 : ℝ) (3/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(194161857/16777216 : ℝ) := by
  have hta : 0≤t-(5/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(3/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(194161857/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(194161857/16777216 : ℝ)=(37596387807 : ℝ)*(t-(5/16 : ℝ))^0*((3/8 : ℝ)-t)^8 + (266986858704 : ℝ)*(t-(5/16 : ℝ))^1*((3/8 : ℝ)-t)^7 + (811838426640 : ℝ)*(t-(5/16 : ℝ))^2*((3/8 : ℝ)-t)^6 + (1370236470464 : ℝ)*(t-(5/16 : ℝ))^3*((3/8 : ℝ)-t)^5 + (1386426062752 : ℝ)*(t-(5/16 : ℝ))^4*((3/8 : ℝ)-t)^4 + (840964932352 : ℝ)*(t-(5/16 : ℝ))^5*((3/8 : ℝ)-t)^3 + (283151863040 : ℝ)*(t-(5/16 : ℝ))^6*((3/8 : ℝ)-t)^2 + (40824478720 : ℝ)*(t-(5/16 : ℝ))^7*((3/8 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(194161857/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (194161857/16777216 : ℝ)-kernelFourthDensityPolynomial t=(61814482977 : ℝ)*(t-(5/16 : ℝ))^0*((3/8 : ℝ)-t)^8 + (528300107568 : ℝ)*(t-(5/16 : ℝ))^1*((3/8 : ℝ)-t)^7 + (1971665955312 : ℝ)*(t-(5/16 : ℝ))^2*((3/8 : ℝ)-t)^6 + (4196772293440 : ℝ)*(t-(5/16 : ℝ))^3*((3/8 : ℝ)-t)^5 + (5572334892128 : ℝ)*(t-(5/16 : ℝ))^4*((3/8 : ℝ)-t)^4 + (4726043831552 : ℝ)*(t-(5/16 : ℝ))^5*((3/8 : ℝ)-t)^3 + (2500352518912 : ℝ)*(t-(5/16 : ℝ))^6*((3/8 : ℝ)-t)^2 + (754462487552 : ℝ)*(t-(5/16 : ℝ))^7*((3/8 : ℝ)-t)^1 + (99410870784 : ℝ)*(t-(5/16 : ℝ))^8*((3/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_5 :
    (∫ t in (5/16 : ℝ)..(3/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(194161857/268435456 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (5/16 : ℝ) (3/8 : ℝ) (194161857/16777216 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_5 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_6 (t : ℝ) (ht : t ∈ Icc (3/8 : ℝ) (7/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(92495694977/4294967296 : ℝ) := by
  have hta : 0≤t-(3/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(7/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(92495694977/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(92495694977/4294967296 : ℝ)=(42790259585 : ℝ)*(t-(3/8 : ℝ))^0*((7/16 : ℝ)-t)^8 + (301497597960 : ℝ)*(t-(3/8 : ℝ))^1*((7/16 : ℝ)-t)^7 + (909736429340 : ℝ)*(t-(3/8 : ℝ))^2*((7/16 : ℝ)-t)^6 + (1523855748408 : ℝ)*(t-(3/8 : ℝ))^3*((7/16 : ℝ)-t)^5 + (1530352650982 : ℝ)*(t-(3/8 : ℝ))^4*((7/16 : ℝ)-t)^4 + (921419277432 : ℝ)*(t-(3/8 : ℝ))^5*((7/16 : ℝ)-t)^3 + (307975219884 : ℝ)*(t-(3/8 : ℝ))^6*((7/16 : ℝ)-t)^2 + (44081935992 : ℝ)*(t-(3/8 : ℝ))^7*((7/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(92495694977/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (92495694977/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(142201130369 : ℝ)*(t-(3/8 : ℝ))^0*((7/16 : ℝ)-t)^8 + (1178433521672 : ℝ)*(t-(3/8 : ℝ))^1*((7/16 : ℝ)-t)^7 + (4270022489372 : ℝ)*(t-(3/8 : ℝ))^2*((7/16 : ℝ)-t)^6 + (8835662089016 : ℝ)*(t-(3/8 : ℝ))^3*((7/16 : ℝ)-t)^5 + (11419044645798 : ℝ)*(t-(3/8 : ℝ))^4*((7/16 : ℝ)-t)^4 + (9438098559992 : ℝ)*(t-(3/8 : ℝ))^5*((7/16 : ℝ)-t)^3 + (4871783698828 : ℝ)*(t-(3/8 : ℝ))^6*((7/16 : ℝ)-t)^2 + (1435849183640 : ℝ)*(t-(3/8 : ℝ))^7*((7/16 : ℝ)-t)^1 + (184991389954 : ℝ)*(t-(3/8 : ℝ))^8*((7/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_6 :
    (∫ t in (3/8 : ℝ)..(7/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(92495694977/68719476736 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (3/8 : ℝ) (7/16 : ℝ) (92495694977/4294967296 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_6 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_7 (t : ℝ) (ht : t ∈ Icc (7/16 : ℝ) (1/2 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(8133/256 : ℝ) := by
  have hta : 0≤t-(7/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1/2 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(8133/256 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(8133/256 : ℝ)=(43953402751 : ℝ)*(t-(7/16 : ℝ))^0*((1/2 : ℝ)-t)^8 + (307545286016 : ℝ)*(t-(7/16 : ℝ))^1*((1/2 : ℝ)-t)^7 + (921523393024 : ℝ)*(t-(7/16 : ℝ))^2*((1/2 : ℝ)-t)^6 + (1532791291904 : ℝ)*(t-(7/16 : ℝ))^3*((1/2 : ℝ)-t)^5 + (1528469184512 : ℝ)*(t-(7/16 : ℝ))^4*((1/2 : ℝ)-t)^4 + (913735942144 : ℝ)*(t-(7/16 : ℝ))^5*((1/2 : ℝ)-t)^3 + (303210430464 : ℝ)*(t-(7/16 : ℝ))^6*((1/2 : ℝ)-t)^2 + (43083890688 : ℝ)*(t-(7/16 : ℝ))^7*((1/2 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(8133/256 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (8133/256 : ℝ)-kernelFourthDensityPolynomial t=(228944792705 : ℝ)*(t-(7/16 : ℝ))^0*((1/2 : ℝ)-t)^8 + (1875640277632 : ℝ)*(t-(7/16 : ℝ))^1*((1/2 : ℝ)-t)^7 + (6719626079744 : ℝ)*(t-(7/16 : ℝ))^2*((1/2 : ℝ)-t)^6 + (13749507653632 : ℝ)*(t-(7/16 : ℝ))^3*((1/2 : ℝ)-t)^5 + (17574404497408 : ℝ)*(t-(7/16 : ℝ))^4*((1/2 : ℝ)-t)^4 + (14368563003392 : ℝ)*(t-(7/16 : ℝ))^5*((1/2 : ℝ)-t)^3 + (7337939042304 : ℝ)*(t-(7/16 : ℝ))^6*((1/2 : ℝ)-t)^2 + (2140101672960 : ℝ)*(t-(7/16 : ℝ))^7*((1/2 : ℝ)-t)^1 + (272898195456 : ℝ)*(t-(7/16 : ℝ))^8*((1/2 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_7 :
    (∫ t in (7/16 : ℝ)..(1/2 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(8133/4096 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (7/16 : ℝ) (1/2 : ℝ) (8133/256 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_7 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 0 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_8 (t : ℝ) (ht : t ∈ Icc (1/2 : ℝ) (9/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(177136684929/4294967296 : ℝ) := by
  have hta : 0≤t-(1/2 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(9/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(177136684929/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(177136684929/4294967296 : ℝ)=(40687587201 : ℝ)*(t-(1/2 : ℝ))^0*((9/16 : ℝ)-t)^8 + (282416806920 : ℝ)*(t-(1/2 : ℝ))^1*((9/16 : ℝ)-t)^7 + (839288402460 : ℝ)*(t-(1/2 : ℝ))^2*((9/16 : ℝ)-t)^6 + (1384247288888 : ℝ)*(t-(1/2 : ℝ))^3*((9/16 : ℝ)-t)^5 + (1368377302342 : ℝ)*(t-(1/2 : ℝ))^4*((9/16 : ℝ)-t)^4 + (810719470648 : ℝ)*(t-(1/2 : ℝ))^5*((9/16 : ℝ)-t)^3 + (266541909020 : ℝ)*(t-(1/2 : ℝ))^6*((9/16 : ℝ)-t)^2 + (37511634568 : ℝ)*(t-(1/2 : ℝ))^7*((9/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(177136684929/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (177136684929/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(313585782657 : ℝ)*(t-(1/2 : ℝ))^0*((9/16 : ℝ)-t)^8 + (2551770151944 : ℝ)*(t-(1/2 : ℝ))^1*((9/16 : ℝ)-t)^7 + (9080365953564 : ℝ)*(t-(1/2 : ℝ))^2*((9/16 : ℝ)-t)^6 + (18455061423160 : ℝ)*(t-(1/2 : ℝ))^3*((9/16 : ℝ)-t)^5 + (23430758587718 : ℝ)*(t-(1/2 : ℝ))^4*((9/16 : ℝ)-t)^4 + (19028589241400 : ℝ)*(t-(1/2 : ℝ))^5*((9/16 : ℝ)-t)^3 + (9653112447004 : ℝ)*(t-(1/2 : ℝ))^6*((9/16 : ℝ)-t)^2 + (2796675324296 : ℝ)*(t-(1/2 : ℝ))^7*((9/16 : ℝ)-t)^1 + (354273369858 : ℝ)*(t-(1/2 : ℝ))^8*((9/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_8 :
    (∫ t in (1/2 : ℝ)..(9/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(59045561643/21474836480 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (1/2 : ℝ) (9/16 : ℝ) (177136684929/4294967296 : ℝ) (16/15 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_8 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 1 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_9 (t : ℝ) (ht : t ∈ Icc (9/16 : ℝ) (5/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(819924545/16777216 : ℝ) := by
  have hta : 0≤t-(9/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(5/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(819924545/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(819924545/16777216 : ℝ)=(32763998591 : ℝ)*(t-(9/16 : ℝ))^0*((5/8 : ℝ)-t)^8 + (224600354160 : ℝ)*(t-(9/16 : ℝ))^1*((5/8 : ℝ)-t)^7 + (658770985616 : ℝ)*(t-(9/16 : ℝ))^2*((5/8 : ℝ)-t)^6 + (1071590054976 : ℝ)*(t-(9/16 : ℝ))^3*((5/8 : ℝ)-t)^5 + (1043919359392 : ℝ)*(t-(9/16 : ℝ))^4*((5/8 : ℝ)-t)^4 + (608966310144 : ℝ)*(t-(9/16 : ℝ))^5*((5/8 : ℝ)-t)^3 + (196933969152 : ℝ)*(t-(9/16 : ℝ))^6*((5/8 : ℝ)-t)^2 + (27231593472 : ℝ)*(t-(9/16 : ℝ))^7*((5/8 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(819924545/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (819924545/16777216 : ℝ)-kernelFourthDensityPolynomial t=(387037368449 : ℝ)*(t-(9/16 : ℝ))^0*((5/8 : ℝ)-t)^8 + (3133810582160 : ℝ)*(t-(9/16 : ℝ))^1*((5/8 : ℝ)-t)^7 + (11095667291504 : ℝ)*(t-(9/16 : ℝ))^2*((5/8 : ℝ)-t)^6 + (22437286499264 : ℝ)*(t-(9/16 : ℝ))^3*((5/8 : ℝ)-t)^5 + (28342176333408 : ℝ)*(t-(9/16 : ℝ))^4*((5/8 : ℝ)-t)^4 + (22899910244096 : ℝ)*(t-(9/16 : ℝ))^5*((5/8 : ℝ)-t)^3 + (11557504307968 : ℝ)*(t-(9/16 : ℝ))^6*((5/8 : ℝ)-t)^2 + (3331179342848 : ℝ)*(t-(9/16 : ℝ))^7*((5/8 : ℝ)-t)^1 + (419801367040 : ℝ)*(t-(9/16 : ℝ))^8*((5/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_9 :
    (∫ t in (9/16 : ℝ)..(5/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(163984909/47185920 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (9/16 : ℝ) (5/8 : ℝ) (819924545/16777216 : ℝ) (256/225 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_9 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 2 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_10 (t : ℝ) (ht : t ∈ Icc (5/8 : ℝ) (11/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(230056003617/4294967296 : ℝ) := by
  have hta : 0≤t-(5/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(11/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(230056003617/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(230056003617/4294967296 : ℝ)=(20155320097 : ℝ)*(t-(5/8 : ℝ))^0*((11/16 : ℝ)-t)^8 + (134010967304 : ℝ)*(t-(5/8 : ℝ))^1*((11/16 : ℝ)-t)^7 + (380040623260 : ℝ)*(t-(5/8 : ℝ))^2*((11/16 : ℝ)-t)^6 + (595485393464 : ℝ)*(t-(5/8 : ℝ))^3*((11/16 : ℝ)-t)^5 + (556320641702 : ℝ)*(t-(5/8 : ℝ))^4*((11/16 : ℝ)-t)^4 + (309553059832 : ℝ)*(t-(5/8 : ℝ))^5*((11/16 : ℝ)-t)^3 + (94861215660 : ℝ)*(t-(5/8 : ℝ))^6*((11/16 : ℝ)-t)^2 + (12328380120 : ℝ)*(t-(5/8 : ℝ))^7*((11/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(230056003617/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (230056003617/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(439956687137 : ℝ)*(t-(5/8 : ℝ))^0*((11/16 : ℝ)-t)^8 + (3546885090568 : ℝ)*(t-(5/8 : ℝ))^1*((11/16 : ℝ)-t)^7 + (12503095579292 : ℝ)*(t-(5/8 : ℝ))^2*((11/16 : ℝ)-t)^6 + (25170787011640 : ℝ)*(t-(5/8 : ℝ))^3*((11/16 : ℝ)-t)^5 + (31651519864678 : ℝ)*(t-(5/8 : ℝ))^4*((11/16 : ℝ)-t)^4 + (25456719345272 : ℝ)*(t-(5/8 : ℝ))^5*((11/16 : ℝ)-t)^3 + (12788274986892 : ℝ)*(t-(5/8 : ℝ))^6*((11/16 : ℝ)-t)^2 + (3668567677752 : ℝ)*(t-(5/8 : ℝ))^7*((11/16 : ℝ)-t)^1 + (460112007234 : ℝ)*(t-(5/8 : ℝ))^8*((11/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_10 :
    (∫ t in (5/8 : ℝ)..(11/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(76685334539/18874368000 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (5/8 : ℝ) (11/16 : ℝ) (230056003617/4294967296 : ℝ) (4096/3375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_10 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 3 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_11 (t : ℝ) (ht : t ∈ Icc (11/16 : ℝ) (3/4 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(229078495/4194304 : ℝ) := by
  have hta : 0≤t-(11/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(3/4 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(229078495/4194304 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(229078495/4194304 : ℝ)=(4520375263 : ℝ)*(t-(11/16 : ℝ))^0*((3/4 : ℝ)-t)^8 + (23834621984 : ℝ)*(t-(11/16 : ℝ))^1*((3/4 : ℝ)-t)^7 + (48834401344 : ℝ)*(t-(11/16 : ℝ))^2*((3/4 : ℝ)-t)^6 + (46338612736 : ℝ)*(t-(11/16 : ℝ))^3*((3/4 : ℝ)-t)^5 + (16942817792 : ℝ)*(t-(11/16 : ℝ))^4*((3/4 : ℝ)-t)^4 + (3169701888 : ℝ)*(t-(11/16 : ℝ))^6*((3/4 : ℝ)-t)^2 + (4744667136 : ℝ)*(t-(11/16 : ℝ))^7*((3/4 : ℝ)-t)^1 + (1450605568 : ℝ)*(t-(11/16 : ℝ))^8*((3/4 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(229078495/4194304 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (229078495/4194304 : ℝ)-kernelFourthDensityPolynomial t=(464632382497 : ℝ)*(t-(11/16 : ℝ))^0*((3/4 : ℝ)-t)^8 + (3729387440096 : ℝ)*(t-(11/16 : ℝ))^1*((3/4 : ℝ)-t)^7 + (13087442815936 : ℝ)*(t-(11/16 : ℝ))^2*((3/4 : ℝ)-t)^6 + (26226215821824 : ℝ)*(t-(11/16 : ℝ))^3*((3/4 : ℝ)-t)^5 + (32823750225408 : ℝ)*(t-(11/16 : ℝ))^4*((3/4 : ℝ)-t)^4 + (26272554434560 : ℝ)*(t-(11/16 : ℝ))^5*((3/4 : ℝ)-t)^3 + (13133107515392 : ℝ)*(t-(11/16 : ℝ))^6*((3/4 : ℝ)-t)^2 + (3748477394944 : ℝ)*(t-(11/16 : ℝ))^7*((3/4 : ℝ)-t)^1 + (467702152192 : ℝ)*(t-(11/16 : ℝ))^8*((3/4 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_11 :
    (∫ t in (11/16 : ℝ)..(3/4 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(45815699/10368000 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (11/16 : ℝ) (3/4 : ℝ) (229078495/4194304 : ℝ) (65536/50625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_11 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 4 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_12 (t : ℝ) (ht : t ∈ Icc (3/4 : ℝ) (13/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(3557217/65536 : ℝ) := by
  have hta : 0≤t-(3/4 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(13/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(3557217/65536 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(3557217/65536 : ℝ)=(6860177408 : ℝ)*(t-(3/4 : ℝ))^1*((13/16 : ℝ)-t)^7 + (58595229696 : ℝ)*(t-(3/4 : ℝ))^2*((13/16 : ℝ)-t)^6 + (208121765888 : ℝ)*(t-(3/4 : ℝ))^3*((13/16 : ℝ)-t)^5 + (401753979392 : ℝ)*(t-(3/4 : ℝ))^4*((13/16 : ℝ)-t)^4 + (457593901568 : ℝ)*(t-(3/4 : ℝ))^5*((13/16 : ℝ)-t)^3 + (308610711616 : ℝ)*(t-(3/4 : ℝ))^6*((13/16 : ℝ)-t)^2 + (114396942560 : ℝ)*(t-(3/4 : ℝ))^7*((13/16 : ℝ)-t)^1 + (18012866719 : ℝ)*(t-(3/4 : ℝ))^8*((13/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(3557217/65536 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (3557217/65536 : ℝ)-kernelFourthDensityPolynomial t=(466251546624 : ℝ)*(t-(3/4 : ℝ))^0*((13/16 : ℝ)-t)^8 + (3723152195584 : ℝ)*(t-(3/4 : ℝ))^1*((13/16 : ℝ)-t)^7 + (12996448075776 : ℝ)*(t-(3/4 : ℝ))^2*((13/16 : ℝ)-t)^6 + (25901964845056 : ℝ)*(t-(3/4 : ℝ))^3*((13/16 : ℝ)-t)^5 + (32235854284288 : ℝ)*(t-(3/4 : ℝ))^4*((13/16 : ℝ)-t)^4 + (25652492709376 : ℝ)*(t-(3/4 : ℝ))^5*((13/16 : ℝ)-t)^3 + (12746432593856 : ℝ)*(t-(3/4 : ℝ))^6*((13/16 : ℝ)-t)^2 + (3615615430432 : ℝ)*(t-(3/4 : ℝ))^7*((13/16 : ℝ)-t)^1 + (448238679905 : ℝ)*(t-(3/4 : ℝ))^8*((13/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_12 :
    (∫ t in (3/4 : ℝ)..(13/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(1185739/253125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (3/4 : ℝ) (13/16 : ℝ) (3557217/65536 : ℝ) (1048576/759375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_12 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 5 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_13 (t : ℝ) (ht : t ∈ Icc (13/16 : ℝ) (7/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(215112906593/4294967296 : ℝ) := by
  have hta : 0≤t-(13/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(7/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(215112906593/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(215112906593/4294967296 : ℝ)=(29705991192 : ℝ)*(t-(13/16 : ℝ))^1*((7/8 : ℝ)-t)^7 + (220134320172 : ℝ)*(t-(13/16 : ℝ))^2*((7/8 : ℝ)-t)^6 + (697435216632 : ℝ)*(t-(13/16 : ℝ))^3*((7/8 : ℝ)-t)^5 + (1224823798822 : ℝ)*(t-(13/16 : ℝ))^4*((7/8 : ℝ)-t)^4 + (1287916655672 : ℝ)*(t-(13/16 : ℝ))^5*((7/8 : ℝ)-t)^3 + (810970294172 : ℝ)*(t-(13/16 : ℝ))^6*((7/8 : ℝ)-t)^2 + (283173715720 : ℝ)*(t-(13/16 : ℝ))^7*((7/8 : ℝ)-t)^1 + (42303166049 : ℝ)*(t-(13/16 : ℝ))^8*((7/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(215112906593/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (215112906593/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(430225813186 : ℝ)*(t-(13/16 : ℝ))^0*((7/8 : ℝ)-t)^8 + (3412100514296 : ℝ)*(t-(13/16 : ℝ))^1*((7/8 : ℝ)-t)^7 + (11826188449036 : ℝ)*(t-(13/16 : ℝ))^2*((7/8 : ℝ)-t)^6 + (23395210321784 : ℝ)*(t-(13/16 : ℝ))^3*((7/8 : ℝ)-t)^5 + (28890983124198 : ℝ)*(t-(13/16 : ℝ))^4*((7/8 : ℝ)-t)^4 + (22804728882744 : ℝ)*(t-(13/16 : ℝ))^5*((7/8 : ℝ)-t)^3 + (11235352475036 : ℝ)*(t-(13/16 : ℝ))^6*((7/8 : ℝ)-t)^2 + (3158632789768 : ℝ)*(t-(13/16 : ℝ))^7*((7/8 : ℝ)-t)^1 + (387922647137 : ℝ)*(t-(13/16 : ℝ))^8*((7/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_13 :
    (∫ t in (13/16 : ℝ)..(7/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(215112906593/46656000000 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (13/16 : ℝ) (7/8 : ℝ) (215112906593/4294967296 : ℝ) (16777216/11390625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_13 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 6 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_14 (t : ℝ) (ht : t ∈ Icc (7/8 : ℝ) (15/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(675038049/16777216 : ℝ) := by
  have hta : 0≤t-(7/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(15/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(675038049/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(675038049/16777216 : ℝ)=(55251612672 : ℝ)*(t-(7/8 : ℝ))^1*((15/16 : ℝ)-t)^7 + (400004222208 : ℝ)*(t-(7/8 : ℝ))^2*((15/16 : ℝ)-t)^6 + (1239975845120 : ℝ)*(t-(7/8 : ℝ))^3*((15/16 : ℝ)-t)^5 + (2133558842272 : ℝ)*(t-(7/8 : ℝ))^4*((15/16 : ℝ)-t)^4 + (2200751472448 : ℝ)*(t-(7/8 : ℝ))^5*((15/16 : ℝ)-t)^3 + (1360880286224 : ℝ)*(t-(7/8 : ℝ))^6*((15/16 : ℝ)-t)^2 + (467126342704 : ℝ)*(t-(7/8 : ℝ))^7*((15/16 : ℝ)-t)^1 + (68661922239 : ℝ)*(t-(7/8 : ℝ))^8*((15/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(675038049/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (675038049/16777216 : ℝ)-kernelFourthDensityPolynomial t=(345619481088 : ℝ)*(t-(7/8 : ℝ))^0*((15/16 : ℝ)-t)^8 + (2709704236032 : ℝ)*(t-(7/8 : ℝ))^1*((15/16 : ℝ)-t)^7 + (9277341248256 : ℝ)*(t-(7/8 : ℝ))^2*((15/16 : ℝ)-t)^6 + (18114715095808 : ℝ)*(t-(7/8 : ℝ))^3*((15/16 : ℝ)-t)^5 + (22059804833888 : ℝ)*(t-(7/8 : ℝ))^4*((15/16 : ℝ)-t)^4 + (17153939468480 : ℝ)*(t-(7/8 : ℝ))^5*((15/16 : ℝ)-t)^3 + (8316465184240 : ℝ)*(t-(7/8 : ℝ))^6*((15/16 : ℝ)-t)^2 + (2297829506000 : ℝ)*(t-(7/8 : ℝ))^7*((15/16 : ℝ)-t)^1 + (276957558849 : ℝ)*(t-(7/8 : ℝ))^8*((15/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_14 :
    (∫ t in (7/8 : ℝ)..(15/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(225012683/56953125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (7/8 : ℝ) (15/16 : ℝ) (675038049/16777216 : ℝ) (268435456/170859375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_14 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 7 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_15 (t : ℝ) (ht : t ∈ Icc (15/16 : ℝ) (1 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(104147818305/4294967296 : ℝ) := by
  have hta : 0≤t-(15/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(1 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(104147818305/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(104147818305/4294967296 : ℝ)=(82169035208 : ℝ)*(t-(15/16 : ℝ))^1*((1 : ℝ)-t)^7 + (588712956444 : ℝ)*(t-(15/16 : ℝ))^2*((1 : ℝ)-t)^6 + (1806672692792 : ℝ)*(t-(15/16 : ℝ))^3*((1 : ℝ)-t)^5 + (3078503685062 : ℝ)*(t-(15/16 : ℝ))^4*((1 : ℝ)-t)^4 + (3145626883640 : ℝ)*(t-(15/16 : ℝ))^5*((1 : ℝ)-t)^3 + (1927440796444 : ℝ)*(t-(15/16 : ℝ))^6*((1 : ℝ)-t)^2 + (655746710024 : ℝ)*(t-(15/16 : ℝ))^7*((1 : ℝ)-t)^1 + (95557883713 : ℝ)*(t-(15/16 : ℝ))^8*((1 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(104147818305/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (104147818305/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(208295636610 : ℝ)*(t-(15/16 : ℝ))^0*((1 : ℝ)-t)^8 + (1584196057672 : ℝ)*(t-(15/16 : ℝ))^1*((1 : ℝ)-t)^7 + (5243564868636 : ℝ)*(t-(15/16 : ℝ))^2*((1 : ℝ)-t)^6 + (9857882957368 : ℝ)*(t-(15/16 : ℝ))^3*((1 : ℝ)-t)^5 + (11502190877638 : ℝ)*(t-(15/16 : ℝ))^4*((1 : ℝ)-t)^4 + (8518928766520 : ℝ)*(t-(15/16 : ℝ))^5*((1 : ℝ)-t)^3 + (3904837028636 : ℝ)*(t-(15/16 : ℝ))^6*((1 : ℝ)-t)^2 + (1010618382856 : ℝ)*(t-(15/16 : ℝ))^7*((1 : ℝ)-t)^1 + (112737752897 : ℝ)*(t-(15/16 : ℝ))^8*((1 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_15 :
    (∫ t in (15/16 : ℝ)..(1 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(6943187887/2733750000 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (15/16 : ℝ) (1 : ℝ) (104147818305/4294967296 : ℝ) (4294967296/2562890625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_15 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 8 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_16 (t : ℝ) (ht : t ∈ Icc (1 : ℝ) (17/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(112433399103/4294967296 : ℝ) := by
  have hta : 0≤t-(1 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(17/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(112433399103/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(112433399103/4294967296 : ℝ)=(103843464511 : ℝ)*(t-(1 : ℝ))^0*((17/16 : ℝ)-t)^8 + (939464075768 : ℝ)*(t-(1 : ℝ))^1*((17/16 : ℝ)-t)^7 + (3681466094308 : ℝ)*(t-(1 : ℝ))^2*((17/16 : ℝ)-t)^6 + (8174863459784 : ℝ)*(t-(1 : ℝ))^3*((17/16 : ℝ)-t)^5 + (11264424243002 : ℝ)*(t-(1 : ℝ))^4*((17/16 : ℝ)-t)^4 + (9872371398088 : ℝ)*(t-(1 : ℝ))^5*((17/16 : ℝ)-t)^3 + (5378340436452 : ℝ)*(t-(1 : ℝ))^6*((17/16 : ℝ)-t)^2 + (1666242102840 : ℝ)*(t-(1 : ℝ))^7*((17/16 : ℝ)-t)^1 + (224866798206 : ℝ)*(t-(1 : ℝ))^8*((17/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(112433399103/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (112433399103/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(121023333695 : ℝ)*(t-(1 : ℝ))^0*((17/16 : ℝ)-t)^8 + (859470309880 : ℝ)*(t-(1 : ℝ))^1*((17/16 : ℝ)-t)^7 + (2614804255460 : ℝ)*(t-(1 : ℝ))^2*((17/16 : ℝ)-t)^6 + (4417677239752 : ℝ)*(t-(1 : ℝ))^3*((17/16 : ℝ)-t)^5 + (4476251631418 : ℝ)*(t-(1 : ℝ))^4*((17/16 : ℝ)-t)^4 + (2720169301448 : ℝ)*(t-(1 : ℝ))^5*((17/16 : ℝ)-t)^3 + (917929913316 : ℝ)*(t-(1 : ℝ))^6*((17/16 : ℝ)-t)^2 + (132692282808 : ℝ)*(t-(1 : ℝ))^7*((17/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_16 :
    (∫ t in (1 : ℝ)..(17/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(37477799701/12814453125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (1 : ℝ) (17/16 : ℝ) (112433399103/4294967296 : ℝ) (68719476736/38443359375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_16 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 9 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_17 (t : ℝ) (ht : t ∈ Icc (17/16 : ℝ) (9/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(996253407/16777216 : ℝ) := by
  have hta : 0≤t-(17/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(9/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(996253407/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(996253407/16777216 : ℝ)=(367474271295 : ℝ)*(t-(17/16 : ℝ))^0*((9/8 : ℝ)-t)^8 + (3072486453168 : ℝ)*(t-(17/16 : ℝ))^1*((9/8 : ℝ)-t)^7 + (11229041642256 : ℝ)*(t-(17/16 : ℝ))^2*((9/8 : ℝ)-t)^6 + (23429721290048 : ℝ)*(t-(17/16 : ℝ))^3*((9/8 : ℝ)-t)^5 + (30526684760992 : ℝ)*(t-(17/16 : ℝ))^4*((9/8 : ℝ)-t)^4 + (25431887680768 : ℝ)*(t-(17/16 : ℝ))^5*((9/8 : ℝ)-t)^3 + (13230078592256 : ℝ)*(t-(17/16 : ℝ))^6*((9/8 : ℝ)-t)^2 + (3929265587200 : ℝ)*(t-(17/16 : ℝ))^7*((9/8 : ℝ)-t)^1 + (510081744384 : ℝ)*(t-(17/16 : ℝ))^8*((9/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(996253407/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (996253407/16777216 : ℝ)-kernelFourthDensityPolynomial t=(142607473089 : ℝ)*(t-(17/16 : ℝ))^0*((9/8 : ℝ)-t)^8 + (1008167501904 : ℝ)*(t-(17/16 : ℝ))^1*((9/8 : ℝ)-t)^7 + (3053247200496 : ℝ)*(t-(17/16 : ℝ))^2*((9/8 : ℝ)-t)^6 + (5134856395456 : ℝ)*(t-(17/16 : ℝ))^3*((9/8 : ℝ)-t)^5 + (5179037345888 : ℝ)*(t-(17/16 : ℝ))^4*((9/8 : ℝ)-t)^4 + (3132690004736 : ℝ)*(t-(17/16 : ℝ))^5*((9/8 : ℝ)-t)^3 + (1052210250496 : ℝ)*(t-(17/16 : ℝ))^6*((9/8 : ℝ)-t)^2 + (151388367872 : ℝ)*(t-(17/16 : ℝ))^7*((9/8 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_17 :
    (∫ t in (17/16 : ℝ)..(9/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(453405995008/64072265625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (17/16 : ℝ) (9/8 : ℝ) (996253407/16777216 : ℝ) (1099511627776/576650390625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_17 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 10 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_18 (t : ℝ) (ht : t ∈ Icc (9/8 : ℝ) (19/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(412368437791/4294967296 : ℝ) := by
  have hta : 0≤t-(9/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(19/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(412368437791/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(412368437791/4294967296 : ℝ)=(667409309983 : ℝ)*(t-(9/8 : ℝ))^0*((19/16 : ℝ)-t)^8 + (5490662847736 : ℝ)*(t-(9/8 : ℝ))^1*((19/16 : ℝ)-t)^7 + (19754687579236 : ℝ)*(t-(9/8 : ℝ))^2*((19/16 : ℝ)-t)^6 + (40597711259080 : ℝ)*(t-(9/8 : ℝ))^3*((19/16 : ℝ)-t)^5 + (52122642374682 : ℝ)*(t-(9/8 : ℝ))^4*((19/16 : ℝ)-t)^4 + (42808925105800 : ℝ)*(t-(9/8 : ℝ))^5*((19/16 : ℝ)-t)^3 + (21964179020276 : ℝ)*(t-(9/8 : ℝ))^6*((19/16 : ℝ)-t)^2 + (6436355947144 : ℝ)*(t-(9/8 : ℝ))^7*((19/16 : ℝ)-t)^1 + (824736875582 : ℝ)*(t-(9/8 : ℝ))^8*((19/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(412368437791/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (412368437791/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(157327565599 : ℝ)*(t-(9/8 : ℝ))^0*((19/16 : ℝ)-t)^8 + (1107232156920 : ℝ)*(t-(9/8 : ℝ))^1*((19/16 : ℝ)-t)^7 + (3337944937060 : ℝ)*(t-(9/8 : ℝ))^2*((19/16 : ℝ)-t)^6 + (5587553773512 : ℝ)*(t-(9/8 : ℝ))^3*((19/16 : ℝ)-t)^5 + (5608938916058 : ℝ)*(t-(9/8 : ℝ))^4*((19/16 : ℝ)-t)^4 + (3376339926792 : ℝ)*(t-(9/8 : ℝ))^5*((19/16 : ℝ)-t)^3 + (1128453496020 : ℝ)*(t-(9/8 : ℝ))^6*((19/16 : ℝ)-t)^2 + (161539057512 : ℝ)*(t-(9/8 : ℝ))^7*((19/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_18 :
    (∫ t in (9/8 : ℝ)..(19/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(105566320074496/8649755859375 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (9/8 : ℝ) (19/16 : ℝ) (412368437791/4294967296 : ℝ) (17592186044416/8649755859375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_18 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 11 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_19 (t : ℝ) (ht : t ∈ Icc (19/16 : ℝ) (5/4 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(8758335/65536 : ℝ) := by
  have hta : 0≤t-(19/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(5/4 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(8758335/65536 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(8758335/65536 : ℝ)=(986354680351 : ℝ)*(t-(19/16 : ℝ))^0*((5/4 : ℝ)-t)^8 + (8052376500320 : ℝ)*(t-(19/16 : ℝ))^1*((5/4 : ℝ)-t)^7 + (28751024358976 : ℝ)*(t-(19/16 : ℝ))^2*((5/4 : ℝ)-t)^6 + (58640040905216 : ℝ)*(t-(19/16 : ℝ))^3*((5/4 : ℝ)-t)^5 + (74723014318592 : ℝ)*(t-(19/16 : ℝ))^4*((5/4 : ℝ)-t)^4 + (60914814459904 : ℝ)*(t-(19/16 : ℝ))^5*((5/4 : ℝ)-t)^3 + (31023376515072 : ℝ)*(t-(19/16 : ℝ))^6*((5/4 : ℝ)-t)^2 + (9024510492672 : ℝ)*(t-(19/16 : ℝ))^7*((5/4 : ℝ)-t)^1 + (1147972485120 : ℝ)*(t-(19/16 : ℝ))^8*((5/4 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(8758335/65536 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (8758335/65536 : ℝ)-kernelFourthDensityPolynomial t=(161617804769 : ℝ)*(t-(19/16 : ℝ))^0*((5/4 : ℝ)-t)^8 + (1131403380640 : ℝ)*(t-(19/16 : ℝ))^1*((5/4 : ℝ)-t)^7 + (3392205224384 : ℝ)*(t-(19/16 : ℝ))^2*((5/4 : ℝ)-t)^6 + (5646418261504 : ℝ)*(t-(19/16 : ℝ))^3*((5/4 : ℝ)-t)^5 + (5635059639808 : ℝ)*(t-(19/16 : ℝ))^4*((5/4 : ℝ)-t)^4 + (3371644706816 : ℝ)*(t-(19/16 : ℝ))^5*((5/4 : ℝ)-t)^3 + (1119853068288 : ℝ)*(t-(19/16 : ℝ))^6*((5/4 : ℝ)-t)^2 + (159269388288 : ℝ)*(t-(19/16 : ℝ))^7*((5/4 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_19 :
    (∫ t in (19/16 : ℝ)..(5/4 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(156736509968384/8649755859375 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (19/16 : ℝ) (5/4 : ℝ) (8758335/65536 : ℝ) (281474976710656/129746337890625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_19 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 12 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_20 (t : ℝ) (ht : t ∈ Icc (5/4 : ℝ) (21/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(725262105183/4294967296 : ℝ) := by
  have hta : 0≤t-(5/4 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(21/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(725262105183/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(725262105183/4294967296 : ℝ)=(1299248347743 : ℝ)*(t-(5/4 : ℝ))^0*((21/16 : ℝ)-t)^8 + (10553256170232 : ℝ)*(t-(5/4 : ℝ))^1*((21/16 : ℝ)-t)^7 + (37488872104548 : ℝ)*(t-(5/4 : ℝ))^2*((21/16 : ℝ)-t)^6 + (76069943977160 : ℝ)*(t-(5/4 : ℝ))^3*((21/16 : ℝ)-t)^5 + (96433016393722 : ℝ)*(t-(5/4 : ℝ))^4*((21/16 : ℝ)-t)^4 + (78204003404488 : ℝ)*(t-(5/4 : ℝ))^5*((21/16 : ℝ)-t)^3 + (39619695811748 : ℝ)*(t-(5/4 : ℝ))^6*((21/16 : ℝ)-t)^2 + (11464153316248 : ℝ)*(t-(5/4 : ℝ))^7*((21/16 : ℝ)-t)^1 + (1450524210366 : ℝ)*(t-(5/4 : ℝ))^8*((21/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(725262105183/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (725262105183/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(151275862623 : ℝ)*(t-(5/4 : ℝ))^0*((21/16 : ℝ)-t)^8 + (1050937512696 : ℝ)*(t-(5/4 : ℝ))^1*((21/16 : ℝ)-t)^7 + (3125805785700 : ℝ)*(t-(5/4 : ℝ))^2*((21/16 : ℝ)-t)^6 + (5159411803336 : ℝ)*(t-(5/4 : ℝ))^3*((21/16 : ℝ)-t)^5 + (5103678331898 : ℝ)*(t-(5/4 : ℝ))^4*((21/16 : ℝ)-t)^4 + (3025352376008 : ℝ)*(t-(5/4 : ℝ))^5*((21/16 : ℝ)-t)^3 + (994982078500 : ℝ)*(t-(5/4 : ℝ))^6*((21/16 : ℝ)-t)^2 + (140040366680 : ℝ)*(t-(5/4 : ℝ))^7*((21/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_20 :
    (∫ t in (5/4 : ℝ)..(21/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(15843592441757696/648731689453125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (5/4 : ℝ) (21/16 : ℝ) (725262105183/4294967296 : ℝ) (4503599627370496/1946195068359375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_20 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 13 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_21 (t : ℝ) (ht : t ∈ Icc (21/16 : ℝ) (11/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(3307301503/16777216 : ℝ) := by
  have hta : 0≤t-(21/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(11/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(3307301503/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(3307301503/16777216 : ℝ)=(1571931289951 : ℝ)*(t-(21/16 : ℝ))^0*((11/8 : ℝ)-t)^8 + (12715490686288 : ℝ)*(t-(21/16 : ℝ))^1*((11/8 : ℝ)-t)^7 + (44979659173648 : ℝ)*(t-(21/16 : ℝ))^2*((11/8 : ℝ)-t)^6 + (90877110472384 : ℝ)*(t-(21/16 : ℝ))^3*((11/8 : ℝ)-t)^5 + (114697413685152 : ℝ)*(t-(21/16 : ℝ))^4*((11/8 : ℝ)-t)^4 + (92597705206528 : ℝ)*(t-(21/16 : ℝ))^5*((11/8 : ℝ)-t)^3 + (46696078836992 : ℝ)*(t-(21/16 : ℝ))^6*((11/8 : ℝ)-t)^2 + (13448114990080 : ℝ)*(t-(21/16 : ℝ))^7*((11/8 : ℝ)-t)^1 + (1693338369536 : ℝ)*(t-(21/16 : ℝ))^8*((11/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(3307301503/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (3307301503/16777216 : ℝ)-kernelFourthDensityPolynomial t=(121407079585 : ℝ)*(t-(21/16 : ℝ))^0*((11/8 : ℝ)-t)^8 + (831216270000 : ℝ)*(t-(21/16 : ℝ))^1*((11/8 : ℝ)-t)^7 + (2433815173360 : ℝ)*(t-(21/16 : ℝ))^2*((11/8 : ℝ)-t)^6 + (3949838221632 : ℝ)*(t-(21/16 : ℝ))^3*((11/8 : ℝ)-t)^5 + (3836272182368 : ℝ)*(t-(21/16 : ℝ))^4*((11/8 : ℝ)-t)^4 + (2229243487488 : ℝ)*(t-(21/16 : ℝ))^5*((11/8 : ℝ)-t)^3 + (717395510016 : ℝ)*(t-(21/16 : ℝ))^6*((11/8 : ℝ)-t)^2 + (98591966208 : ℝ)*(t-(21/16 : ℝ))^7*((11/8 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_21 :
    (∫ t in (21/16 : ℝ)..(11/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(887796987087290368/29192926025390625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (21/16 : ℝ) (11/8 : ℝ) (3307301503/16777216 : ℝ) (72057594037927936/29192926025390625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_21 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 14 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_22 (t : ℝ) (ht : t ∈ Icc (11/8 : ℝ) (23/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(913035440127/4294967296 : ℝ) := by
  have hta : 0≤t-(11/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(23/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(913035440127/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(913035440127/4294967296 : ℝ)=(1759704624895 : ℝ)*(t-(11/8 : ℝ))^0*((23/16 : ℝ)-t)^8 + (14176228965368 : ℝ)*(t-(11/8 : ℝ))^1*((23/16 : ℝ)-t)^7 + (49934621513956 : ℝ)*(t-(11/8 : ℝ))^2*((23/16 : ℝ)-t)^6 + (100445681522888 : ℝ)*(t-(11/8 : ℝ))^3*((23/16 : ℝ)-t)^5 + (126197506372442 : ℝ)*(t-(11/8 : ℝ))^4*((23/16 : ℝ)-t)^4 + (101401078730248 : ℝ)*(t-(11/8 : ℝ))^5*((23/16 : ℝ)-t)^3 + (50884769163636 : ℝ)*(t-(11/8 : ℝ))^6*((23/16 : ℝ)-t)^2 + (14579683336680 : ℝ)*(t-(11/8 : ℝ))^7*((23/16 : ℝ)-t)^1 + (1826070880254 : ℝ)*(t-(11/8 : ℝ))^8*((23/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(913035440127/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (913035440127/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(66366255359 : ℝ)*(t-(11/8 : ℝ))^0*((23/16 : ℝ)-t)^8 + (432338076664 : ℝ)*(t-(11/8 : ℝ))^1*((23/16 : ℝ)-t)^7 + (1195363133156 : ℝ)*(t-(11/8 : ℝ))^2*((23/16 : ℝ)-t)^6 + (1814287771336 : ℝ)*(t-(11/8 : ℝ))^3*((23/16 : ℝ)-t)^5 + (1627455245338 : ℝ)*(t-(11/8 : ℝ))^4*((23/16 : ℝ)-t)^4 + (858890563976 : ℝ)*(t-(11/8 : ℝ))^5*((23/16 : ℝ)-t)^3 + (245215483476 : ℝ)*(t-(11/8 : ℝ))^6*((23/16 : ℝ)-t)^2 + (28883705352 : ℝ)*(t-(11/8 : ℝ))^7*((23/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_22 :
    (∫ t in (11/8 : ℝ)..(23/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(5106064264888582144/145964630126953125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (11/8 : ℝ) (23/16 : ℝ) (913035440127/4294967296 : ℝ) (1152921504606846976/437893890380859375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_22 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 15 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_23 (t : ℝ) (ht : t ∈ Icc (23/16 : ℝ) (3/2 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(448804763/2097152 : ℝ) := by
  have hta : 0≤t-(23/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(3/2 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(448804763/2097152 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(448804763/2097152 : ℝ)=(1832187594751 : ℝ)*(t-(23/16 : ℝ))^0*((3/2 : ℝ)-t)^8 + (14686384463360 : ℝ)*(t-(23/16 : ℝ))^1*((3/2 : ℝ)-t)^7 + (51460409044480 : ℝ)*(t-(23/16 : ℝ))^2*((3/2 : ℝ)-t)^6 + (102945041317888 : ℝ)*(t-(23/16 : ℝ))^3*((3/2 : ℝ)-t)^5 + (128589090516992 : ℝ)*(t-(23/16 : ℝ))^4*((3/2 : ℝ)-t)^4 + (102693171314688 : ℝ)*(t-(23/16 : ℝ))^5*((3/2 : ℝ)-t)^3 + (51202069340160 : ℝ)*(t-(23/16 : ℝ))^6*((3/2 : ℝ)-t)^2 + (14571043995648 : ℝ)*(t-(23/16 : ℝ))^7*((3/2 : ℝ)-t)^1 + (1811884595200 : ℝ)*(t-(23/16 : ℝ))^8*((3/2 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(448804763/2097152 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (448804763/2097152 : ℝ)-kernelFourthDensityPolynomial t=(6116714497 : ℝ)*(t-(23/16 : ℝ))^0*((3/2 : ℝ)-t)^8 + (20050010624 : ℝ)*(t-(23/16 : ℝ))^1*((3/2 : ℝ)-t)^7 + (12111614464 : ℝ)*(t-(23/16 : ℝ))^2*((3/2 : ℝ)-t)^6 + (92211130368 : ℝ)*(t-(23/16 : ℝ))^4*((3/2 : ℝ)-t)^4 + (251870003200 : ℝ)*(t-(23/16 : ℝ))^5*((3/2 : ℝ)-t)^3 + (270451318784 : ℝ)*(t-(23/16 : ℝ))^6*((3/2 : ℝ)-t)^2 + (135390478336 : ℝ)*(t-(23/16 : ℝ))^7*((3/2 : ℝ)-t)^1 + (26419714048 : ℝ)*(t-(23/16 : ℝ))^8*((3/2 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_23 :
    (∫ t in (23/16 : ℝ)..(3/2 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(246733027759875948544/6568408355712890625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (23/16 : ℝ) (3/2 : ℝ) (448804763/2097152 : ℝ) (18446744073709551616/6568408355712890625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_23 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 16 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_24 (t : ℝ) (ht : t ∈ Icc (3/2 : ℝ) (25/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(53211/256 : ℝ) := by
  have hta : 0≤t-(3/2 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(25/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(53211/256 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(53211/256 : ℝ)=(1785464881152 : ℝ)*(t-(3/2 : ℝ))^0*((25/16 : ℝ)-t)^8 + (14207751815168 : ℝ)*(t-(3/2 : ℝ))^1*((25/16 : ℝ)-t)^7 + (49398776070144 : ℝ)*(t-(3/2 : ℝ))^2*((25/16 : ℝ)-t)^6 + (98008759795712 : ℝ)*(t-(3/2 : ℝ))^3*((25/16 : ℝ)-t)^5 + (121350585638912 : ℝ)*(t-(3/2 : ℝ))^4*((25/16 : ℝ)-t)^4 + (96004977704960 : ℝ)*(t-(3/2 : ℝ))^5*((25/16 : ℝ)-t)^3 + (47387147537920 : ℝ)*(t-(3/2 : ℝ))^6*((25/16 : ℝ)-t)^2 + (13340018301440 : ℝ)*(t-(3/2 : ℝ))^7*((25/16 : ℝ)-t)^1 + (1639533489151 : ℝ)*(t-(3/2 : ℝ))^8*((25/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(53211/256 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (53211/256 : ℝ)-kernelFourthDensityPolynomial t=(75967234048 : ℝ)*(t-(3/2 : ℝ))^1*((25/16 : ℝ)-t)^7 + (594240602112 : ℝ)*(t-(3/2 : ℝ))^2*((25/16 : ℝ)-t)^6 + (1977273548800 : ℝ)*(t-(3/2 : ℝ))^3*((25/16 : ℝ)-t)^5 + (3631956041728 : ℝ)*(t-(3/2 : ℝ))^4*((25/16 : ℝ)-t)^4 + (3981055639552 : ℝ)*(t-(3/2 : ℝ))^5*((25/16 : ℝ)-t)^3 + (2605869134336 : ℝ)*(t-(3/2 : ℝ))^6*((25/16 : ℝ)-t)^2 + (943700747776 : ℝ)*(t-(3/2 : ℝ))^7*((25/16 : ℝ)-t)^1 + (145931392001 : ℝ)*(t-(3/2 : ℝ))^8*((25/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_24 :
    (∫ t in (3/2 : ℝ)..(25/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(1278085545450727800832/32842041778564453125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (3/2 : ℝ) (25/16 : ℝ) (53211/256 : ℝ) (295147905179352825856/98526125335693359375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_24 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 17 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_25 (t : ℝ) (ht : t ∈ Icc (25/16 : ℝ) (13/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(746801048575/4294967296 : ℝ) := by
  have hta : 0≤t-(25/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(13/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(746801048575/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(746801048575/4294967296 : ℝ)=(1493602097150 : ℝ)*(t-(25/16 : ℝ))^0*((13/8 : ℝ)-t)^8 + (11725066388968 : ℝ)*(t-(25/16 : ℝ))^1*((13/8 : ℝ)-t)^7 + (40168563126644 : ℝ)*(t-(25/16 : ℝ))^2*((13/8 : ℝ)-t)^6 + (78418100616712 : ℝ)*(t-(25/16 : ℝ))^3*((13/8 : ℝ)-t)^5 + (95386846870362 : ℝ)*(t-(25/16 : ℝ))^4*((13/8 : ℝ)-t)^4 + (74002028984520 : ℝ)*(t-(25/16 : ℝ))^5*((13/8 : ℝ)-t)^3 + (35743100348644 : ℝ)*(t-(25/16 : ℝ))^6*((13/8 : ℝ)-t)^2 + (9821728955384 : ℝ)*(t-(25/16 : ℝ))^7*((13/8 : ℝ)-t)^1 + (1174812502783 : ℝ)*(t-(25/16 : ℝ))^8*((13/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(746801048575/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (746801048575/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(223750388232 : ℝ)*(t-(25/16 : ℝ))^1*((13/8 : ℝ)-t)^7 + (1652295593556 : ℝ)*(t-(25/16 : ℝ))^2*((13/8 : ℝ)-t)^6 + (5223616823688 : ℝ)*(t-(25/16 : ℝ))^3*((13/8 : ℝ)-t)^5 + (9165299930138 : ℝ)*(t-(25/16 : ℝ))^4*((13/8 : ℝ)-t)^4 + (9639688455880 : ℝ)*(t-(25/16 : ℝ))^5*((13/8 : ℝ)-t)^3 + (6077758371556 : ℝ)*(t-(25/16 : ℝ))^6*((13/8 : ℝ)-t)^2 + (2127087821816 : ℝ)*(t-(25/16 : ℝ))^7*((13/8 : ℝ)-t)^1 + (318789594367 : ℝ)*(t-(25/16 : ℝ))^8*((13/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_25 :
    (∫ t in (25/16 : ℝ)..(13/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(2052791091358804738048/59115675201416015625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (25/16 : ℝ) (13/8 : ℝ) (746801048575/4294967296 : ℝ) (4722366482869645213696/1477891880035400390625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_25 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 18 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_26 (t : ℝ) (ht : t ∈ Icc (13/8 : ℝ) (27/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(1671919743/16777216 : ℝ) := by
  have hta : 0≤t-(13/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(27/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(1671919743/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(1671919743/16777216 : ℝ)=(856022908416 : ℝ)*(t-(13/8 : ℝ))^0*((27/16 : ℝ)-t)^8 + (6424954334208 : ℝ)*(t-(13/8 : ℝ))^1*((27/16 : ℝ)-t)^7 + (20891786642688 : ℝ)*(t-(13/8 : ℝ))^2*((27/16 : ℝ)-t)^6 + (38353726909184 : ℝ)*(t-(13/8 : ℝ))^3*((27/16 : ℝ)-t)^5 + (43343201947552 : ℝ)*(t-(13/8 : ℝ))^4*((27/16 : ℝ)-t)^4 + (30735143435968 : ℝ)*(t-(13/8 : ℝ))^5*((27/16 : ℝ)-t)^3 + (13262087554832 : ℝ)*(t-(13/8 : ℝ))^6*((27/16 : ℝ)-t)^2 + (3147140829520 : ℝ)*(t-(13/8 : ℝ))^7*((27/16 : ℝ)-t)^1 + (307866455391 : ℝ)*(t-(13/8 : ℝ))^8*((27/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(1671919743/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (1671919743/16777216 : ℝ)-kernelFourthDensityPolynomial t=(423228933120 : ℝ)*(t-(13/8 : ℝ))^1*((27/16 : ℝ)-t)^7 + (3076854792960 : ℝ)*(t-(13/8 : ℝ))^2*((27/16 : ℝ)-t)^6 + (9583555962112 : ℝ)*(t-(13/8 : ℝ))^3*((27/16 : ℝ)-t)^5 + (16578401641568 : ℝ)*(t-(13/8 : ℝ))^4*((27/16 : ℝ)-t)^4 + (17202139435328 : ℝ)*(t-(13/8 : ℝ))^5*((27/16 : ℝ)-t)^3 + (10706553880816 : ℝ)*(t-(13/8 : ℝ))^6*((27/16 : ℝ)-t)^2 + (3701042437808 : ℝ)*(t-(13/8 : ℝ))^7*((27/16 : ℝ)-t)^1 + (548156453025 : ℝ)*(t-(13/8 : ℝ))^8*((27/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_26 :
    (∫ t in (13/8 : ℝ)..(27/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(156867856907670321627136/7389459400177001953125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (13/8 : ℝ) (27/16 : ℝ) (1671919743/16777216 : ℝ) (75557863725914323419136/22168378200531005859375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_26 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 19 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_27 (t : ℝ) (ht : t ∈ Icc (27/16 : ℝ) (7/4 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(14717633/65536 : ℝ) := by
  have hta : 0≤t-(27/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(7/4 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(14717633/65536 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(14717633/65536 : ℝ)=(844389797471 : ℝ)*(t-(27/16 : ℝ))^0*((7/4 : ℝ)-t)^8 + (6070909193376 : ℝ)*(t-(27/16 : ℝ))^1*((7/4 : ℝ)-t)^7 + (18705812523584 : ℝ)*(t-(27/16 : ℝ))^2*((7/4 : ℝ)-t)^6 + (32019556713984 : ℝ)*(t-(27/16 : ℝ))^3*((7/4 : ℝ)-t)^5 + (32884652595712 : ℝ)*(t-(27/16 : ℝ))^4*((7/4 : ℝ)-t)^4 + (20263290691584 : ℝ)*(t-(27/16 : ℝ))^5*((7/4 : ℝ)-t)^3 + (6936514412544 : ℝ)*(t-(27/16 : ℝ))^6*((7/4 : ℝ)-t)^2 + (1017612730368 : ℝ)*(t-(27/16 : ℝ))^7*((7/4 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(14717633/65536 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (14717633/65536 : ℝ)-kernelFourthDensityPolynomial t=(1084679795105 : ℝ)*(t-(27/16 : ℝ))^0*((7/4 : ℝ)-t)^8 + (9361647547232 : ℝ)*(t-(27/16 : ℝ))^1*((7/4 : ℝ)-t)^7 + (35308136068544 : ℝ)*(t-(27/16 : ℝ))^2*((7/4 : ℝ)-t)^6 + (76008340470272 : ℝ)*(t-(27/16 : ℝ))^3*((7/4 : ℝ)-t)^5 + (102150218884608 : ℝ)*(t-(27/16 : ℝ))^4*((7/4 : ℝ)-t)^4 + (87764606492672 : ℝ)*(t-(27/16 : ℝ))^5*((7/4 : ℝ)-t)^3 + (47077434179584 : ℝ)*(t-(27/16 : ℝ))^6*((7/4 : ℝ)-t)^2 + (14414944010240 : ℝ)*(t-(27/16 : ℝ))^7*((7/4 : ℝ)-t)^1 + (1929069592576 : ℝ)*(t-(27/16 : ℝ))^8*((7/4 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_27 :
    (∫ t in (27/16 : ℝ)..(7/4 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(16968275582611383079927808/332525673007965087890625 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (27/16 : ℝ) (7/4 : ℝ) (14717633/65536 : ℝ) (1208925819614629174706176/332525673007965087890625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_27 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 20 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_28 (t : ℝ) (ht : t ∈ Icc (7/4 : ℝ) (29/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(2183534686689/4294967296 : ℝ) := by
  have hta : 0≤t-(7/4 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(29/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(2183534686689/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(2183534686689/4294967296 : ℝ)=(1218999890401 : ℝ)*(t-(7/4 : ℝ))^0*((29/16 : ℝ)-t)^8 + (8734386392840 : ℝ)*(t-(7/4 : ℝ))^1*((29/16 : ℝ)-t)^7 + (26821933118620 : ℝ)*(t-(7/4 : ℝ))^2*((29/16 : ℝ)-t)^6 + (45759406770488 : ℝ)*(t-(7/4 : ℝ))^3*((29/16 : ℝ)-t)^5 + (46841038257542 : ℝ)*(t-(7/4 : ℝ))^4*((29/16 : ℝ)-t)^4 + (28769207251768 : ℝ)*(t-(7/4 : ℝ))^5*((29/16 : ℝ)-t)^3 + (9816580344540 : ℝ)*(t-(7/4 : ℝ))^6*((29/16 : ℝ)-t)^2 + (1435551196008 : ℝ)*(t-(7/4 : ℝ))^7*((29/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(2183534686689/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (2183534686689/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(3148069482977 : ℝ)*(t-(7/4 : ℝ))^0*((29/16 : ℝ)-t)^8 + (26202168594184 : ℝ)*(t-(7/4 : ℝ))^1*((29/16 : ℝ)-t)^7 + (95456009335964 : ℝ)*(t-(7/4 : ℝ))^2*((29/16 : ℝ)-t)^6 + (198796478138680 : ℝ)*(t-(7/4 : ℝ))^3*((29/16 : ℝ)-t)^5 + (258853817878918 : ℝ)*(t-(7/4 : ℝ))^4*((29/16 : ℝ)-t)^4 + (215786677657400 : ℝ)*(t-(7/4 : ℝ))^5*((29/16 : ℝ)-t)^3 + (112461362110044 : ℝ)*(t-(7/4 : ℝ))^6*((29/16 : ℝ)-t)^2 + (33501003791016 : ℝ)*(t-(7/4 : ℝ))^7*((29/16 : ℝ)-t)^1 + (4367069373378 : ℝ)*(t-(7/4 : ℝ))^8*((29/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_28 :
    (∫ t in (7/4 : ℝ)..(29/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(204870125027565273589219328/1662628365039825439453125 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (7/4 : ℝ) (29/16 : ℝ) (2183534686689/4294967296 : ℝ) (19342813113834066795298816/4987885095119476318359375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_28 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 21 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_29 (t : ℝ) (ht : t ∈ Icc (29/16 : ℝ) (15/8 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(15110391585/16777216 : ℝ) := by
  have hta : 0≤t-(29/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(15/8 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(15110391585/16777216 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(15110391585/16777216 : ℝ)=(1684725559071 : ℝ)*(t-(29/16 : ℝ))^0*((15/8 : ℝ)-t)^8 + (12042253276560 : ℝ)*(t-(29/16 : ℝ))^1*((15/8 : ℝ)-t)^7 + (36891179254416 : ℝ)*(t-(29/16 : ℝ))^2*((15/8 : ℝ)-t)^6 + (62788087726016 : ℝ)*(t-(29/16 : ℝ))^3*((15/8 : ℝ)-t)^5 + (64120240664992 : ℝ)*(t-(29/16 : ℝ))^4*((15/8 : ℝ)-t)^4 + (39289425889024 : ℝ)*(t-(29/16 : ℝ))^5*((15/8 : ℝ)-t)^3 + (13375025161472 : ℝ)*(t-(29/16 : ℝ))^6*((15/8 : ℝ)-t)^2 + (1951403748352 : ℝ)*(t-(29/16 : ℝ))^7*((15/8 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(15110391585/16777216 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (15110391585/16777216 : ℝ)-kernelFourthDensityPolynomial t=(6051794932449 : ℝ)*(t-(29/16 : ℝ))^0*((15/8 : ℝ)-t)^8 + (49849910655600 : ℝ)*(t-(29/16 : ℝ))^1*((15/8 : ℝ)-t)^7 + (179731394508144 : ℝ)*(t-(29/16 : ℝ))^2*((15/8 : ℝ)-t)^6 + (370457059799104 : ℝ)*(t-(29/16 : ℝ))^3*((15/8 : ℝ)-t)^5 + (477436193741408 : ℝ)*(t-(29/16 : ℝ))^4*((15/8 : ℝ)-t)^4 + (393955721636096 : ℝ)*(t-(29/16 : ℝ))^5*((15/8 : ℝ)-t)^3 + (203247548601088 : ℝ)*(t-(29/16 : ℝ))^6*((15/8 : ℝ)-t)^2 + (59940760183808 : ℝ)*(t-(29/16 : ℝ))^7*((15/8 : ℝ)-t)^1 + (7736520491520 : ℝ)*(t-(29/16 : ℝ))^8*((15/8 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_29 :
    (∫ t in (29/16 : ℝ)..(15/8 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(1161406360091789285302206464/4987885095119476318359375 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (29/16 : ℝ) (15/8 : ℝ) (15110391585/16777216 : ℝ) (309485009821345068724781056/74818276426792144775390625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_29 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 22 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_30 (t : ℝ) (ht : t ∈ Icc (15/8 : ℝ) (31/16 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(6123873294017/4294967296 : ℝ) := by
  have hta : 0≤t-(15/8 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(31/16 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(6123873294017/4294967296 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(6123873294017/4294967296 : ℝ)=(2255613048257 : ℝ)*(t-(15/8 : ℝ))^0*((31/16 : ℝ)-t)^8 + (16093500637704 : ℝ)*(t-(15/8 : ℝ))^1*((31/16 : ℝ)-t)^7 + (49212538035740 : ℝ)*(t-(15/8 : ℝ))^2*((31/16 : ℝ)-t)^6 + (83607291889464 : ℝ)*(t-(15/8 : ℝ))^3*((31/16 : ℝ)-t)^5 + (85227355302502 : ℝ)*(t-(15/8 : ℝ))^4*((31/16 : ℝ)-t)^4 + (52129059493752 : ℝ)*(t-(15/8 : ℝ))^5*((31/16 : ℝ)-t)^3 + (17714242948140 : ℝ)*(t-(15/8 : ℝ))^6*((31/16 : ℝ)-t)^2 + (2579897313720 : ℝ)*(t-(15/8 : ℝ))^7*((31/16 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(6123873294017/4294967296 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (6123873294017/4294967296 : ℝ)-kernelFourthDensityPolynomial t=(9992133539777 : ℝ)*(t-(15/8 : ℝ))^0*((31/16 : ℝ)-t)^8 + (81888472066568 : ℝ)*(t-(15/8 : ℝ))^1*((31/16 : ℝ)-t)^7 + (293724366429212 : ℝ)*(t-(15/8 : ℝ))^2*((31/16 : ℝ)-t)^6 + (602266517040440 : ℝ)*(t-(15/8 : ℝ))^3*((31/16 : ℝ)-t)^5 + (772114905859878 : ℝ)*(t-(15/8 : ℝ))^4*((31/16 : ℝ)-t)^4 + (633744749436152 : ℝ)*(t-(15/8 : ℝ))^5*((31/16 : ℝ)-t)^3 + (325222661516812 : ℝ)*(t-(15/8 : ℝ))^6*((31/16 : ℝ)-t)^2 + (95402075390552 : ℝ)*(t-(15/8 : ℝ))^7*((31/16 : ℝ)-t)^1 + (12247746588034 : ℝ)*(t-(15/8 : ℝ))^8*((31/16 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_30 :
    (∫ t in (15/8 : ℝ)..(31/16 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(441271575759985489465585958912/1122274146401882171630859375 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (15/8 : ℝ) (31/16 : ℝ) (6123873294017/4294967296 : ℝ) (4951760157141521099596496896/1122274146401882171630859375 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_30 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 23 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_mesh_31 (t : ℝ) (ht : t ∈ Icc (31/16 : ℝ) (2 : ℝ)) :
    |kernelFourthDensityPolynomial t|≤(2112 : ℝ) := by
  have hta : 0≤t-(31/16 : ℝ) := sub_nonneg.mpr ht.1
  have hbt : 0≤(2 : ℝ)-t := sub_nonneg.mpr ht.2
  have hlow : 0≤kernelFourthDensityPolynomial t+(2112 : ℝ) := by
    rw [show kernelFourthDensityPolynomial t+(2112 : ℝ)=(2947097635135 : ℝ)*(t-(31/16 : ℝ))^0*((2 : ℝ)-t)^8 + (20996883767360 : ℝ)*(t-(31/16 : ℝ))^1*((2 : ℝ)-t)^7 + (64114414339840 : ℝ)*(t-(31/16 : ℝ))^2*((2 : ℝ)-t)^6 + (108767949099008 : ℝ)*(t-(31/16 : ℝ))^3*((2 : ℝ)-t)^5 + (110716923871232 : ℝ)*(t-(31/16 : ℝ))^4*((2 : ℝ)-t)^4 + (67623014367232 : ℝ)*(t-(31/16 : ℝ))^5*((2 : ℝ)-t)^3 + (22946600976384 : ℝ)*(t-(31/16 : ℝ))^6*((2 : ℝ)-t)^2 + (3337189588992 : ℝ)*(t-(31/16 : ℝ))^7*((2 : ℝ)-t)^1 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  have hhigh : 0≤(2112 : ℝ)-kernelFourthDensityPolynomial t := by
    rw [show (2112 : ℝ)-kernelFourthDensityPolynomial t=(15194844223169 : ℝ)*(t-(31/16 : ℝ))^0*((2 : ℝ)-t)^8 + (124138651099072 : ℝ)*(t-(31/16 : ℝ))^1*((2 : ℝ)-t)^7 + (443859957692672 : ℝ)*(t-(31/16 : ℝ))^2*((2 : ℝ)-t)^6 + (907180794966016 : ℝ)*(t-(31/16 : ℝ))^3*((2 : ℝ)-t)^5 + (1159219006210048 : ℝ)*(t-(31/16 : ℝ))^4*((2 : ℝ)-t)^4 + (948325729697792 : ℝ)*(t-(31/16 : ℝ))^5*((2 : ℝ)-t)^3 + (485027771056128 : ℝ)*(t-(31/16 : ℝ))^6*((2 : ℝ)-t)^2 + (141798345277440 : ℝ)*(t-(31/16 : ℝ))^7*((2 : ℝ)-t)^1 + (18141941858304 : ℝ)*(t-(31/16 : ℝ))^8*((2 : ℝ)-t)^0 by unfold kernelFourthDensityPolynomial logRawPoly4; ring]
    positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma kernel_fourth_interval_31 :
    (∫ t in (31/16 : ℝ)..(2 : ℝ),|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(3486039150627630854115933814784/5611370732009410858154296875 : ℝ) := by
  have hh := interval_mass_of_mesh_bound kernelFourthDensityPolynomial (by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop)
    (31/16 : ℝ) (2 : ℝ) (2112 : ℝ) (79228162514264337593543950336/16834112196028232574462890625 : ℝ) (by norm_num) (by norm_num)
    kernel_fourth_mesh_31 (fun t ht => ?_)
  · norm_num at hh ⊢
    exact hh
  · have he := exp_mesh_rational_upper (t-1/2) 24 (by linarith [ht.2])
    norm_num at he ⊢
    exact he

lemma kernel_fourth_whole_interval :
    (∫ t in (0 : ℝ)..2,|kernelFourthDensityPolynomial t| * Real.exp (t-1/2))≤(1730 : ℝ) := by
  have hc : Continuous (fun t => |kernelFourthDensityPolynomial t| * Real.exp (t-1/2)) := by unfold kernelFourthDensityPolynomial logRawPoly4; fun_prop
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := fun j : ℕ => (j : ℝ)/16) (n := 32)
    (fun k hk => hc.intervalIntegrable ((k : ℝ)/16) ((k+1 : ℕ)/16 : ℝ))
  norm_num only [Nat.cast_zero,zero_div,Nat.cast_ofNat] at hsum
  rw [← hsum]
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.cast_add,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  have h0 := kernel_fourth_interval_0
  have h1 := kernel_fourth_interval_1
  have h2 := kernel_fourth_interval_2
  have h3 := kernel_fourth_interval_3
  have h4 := kernel_fourth_interval_4
  have h5 := kernel_fourth_interval_5
  have h6 := kernel_fourth_interval_6
  have h7 := kernel_fourth_interval_7
  have h8 := kernel_fourth_interval_8
  have h9 := kernel_fourth_interval_9
  have h10 := kernel_fourth_interval_10
  have h11 := kernel_fourth_interval_11
  have h12 := kernel_fourth_interval_12
  have h13 := kernel_fourth_interval_13
  have h14 := kernel_fourth_interval_14
  have h15 := kernel_fourth_interval_15
  have h16 := kernel_fourth_interval_16
  have h17 := kernel_fourth_interval_17
  have h18 := kernel_fourth_interval_18
  have h19 := kernel_fourth_interval_19
  have h20 := kernel_fourth_interval_20
  have h21 := kernel_fourth_interval_21
  have h22 := kernel_fourth_interval_22
  have h23 := kernel_fourth_interval_23
  have h24 := kernel_fourth_interval_24
  have h25 := kernel_fourth_interval_25
  have h26 := kernel_fourth_interval_26
  have h27 := kernel_fourth_interval_27
  have h28 := kernel_fourth_interval_28
  have h29 := kernel_fourth_interval_29
  have h30 := kernel_fourth_interval_30
  have h31 := kernel_fourth_interval_31
  norm_num at *
  linarith

theorem actual_kernel_fourth_polynomial_moment_bound_complete :
    (∫ t in (0 : ℝ)..2,|t*((128 : ℝ)-452*t-124*t^2+537*t^3+27*t^4-97*t^5-20*t^6-t^7)| *Real.exp (t-1/2)) ≤ 1730 := by
  have he : (fun t : ℝ => |kernelFourthDensityPolynomial t| *Real.exp (t-1/2)) =
      (fun t : ℝ => |t*((128 : ℝ)-452*t-124*t^2+537*t^3+27*t^4-97*t^5-20*t^6-t^7)| *Real.exp (t-1/2)) := by
    funext t
    congr 2
    dsimp [kernelFourthDensityPolynomial,logRawPoly4]
    ring
  rw [← he]
  exact kernel_fourth_whole_interval

end Helfgott
end

open Helfgott

theorem solution :
    (∫ t in (0 : ℝ)..2,|t*((128 : ℝ)-452*t-124*t^2+537*t^3+27*t^4-97*t^5-20*t^6-t^7)| *Real.exp (t-1/2)) ≤ 1730 := Helfgott.actual_kernel_fourth_polynomial_moment_bound_complete

#print axioms solution
