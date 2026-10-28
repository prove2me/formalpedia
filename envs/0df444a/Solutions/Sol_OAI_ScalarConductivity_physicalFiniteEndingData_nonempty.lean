-- Prove2me | solution 1 for OAI.ScalarConductivity.physicalFiniteEndingData_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:19:30.739179+00:00
-- url     : https://prove2.me/submissions/c7871ef0-ae74-4f32-aadd-99a4984ea31d

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C007
import Theorems.Thm_OAI_ScalarConductivity_central_pair_regular_exists
import Theorems.Thm_OAI_ScalarConductivity_elliptic_fourier_matching_regular
import Theorems.Thm_OAI_ScalarConductivity_endingJoin_constitution_ae
import Theorems.Thm_OAI_ScalarConductivity_matchedEnding_regularRegion_ae
import Theorems.Thm_OAI_ScalarConductivity_matchedEnding_weak_equation

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_ModeConnector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma connectorRate_smooth (K : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (connectorRate K) := by
  exact contDiff_const.add (contDiff_const.mul (smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const K)))

lemma connectorRate_bounds (K z : ℝ) : 1/2 ≤ connectorRate K z ∧ connectorRate K z ≤ 3 := by
  have h₁ := smoothTransition.nonneg ((z-1)/K)
  have h₂ := smoothTransition.le_one ((z-1)/K)
  constructor <;> dsimp [connectorRate] <;> linarith

lemma connectorRate_left {K z : ℝ} (hK : 0 < K) (hz : z ≤ 1) :
    connectorRate K z = 1/2 := by
  rw [connectorRate,smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hK.le)]
  ring

lemma connectorRate_hasDerivAt (K z : ℝ) : HasDerivAt (connectorRate K)
    ((5/(2*K))*deriv smoothTransition ((z-1)/K)) z := by
  have h := ((smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
    ((z-1)/K)).hasDerivAt
  have hh := ((h.comp z (((hasDerivAt_id z).sub_const 1).div_const K)).const_mul (5/2)).const_add (1/2)
  have he : (5/2)*(deriv smoothTransition ((z-1)/K)*(1/K)) =
      (5/(2*K))*deriv smoothTransition ((z-1)/K) := by ring
  change HasDerivAt (fun w => 1/2+(5/2)*smoothTransition ((w-1)/K))
    ((5/(2*K))*deriv smoothTransition ((z-1)/K)) z
  exact hh.congr_deriv (g' := (5/(2*K))*deriv smoothTransition ((z-1)/K)) he

lemma connectorRate_derivative_bounds {M K : ℝ} (hM : 1 ≤ M) (hK : 20*M ≤ K)
    (hbound : ∀ x : ℝ, |deriv smoothTransition x| ≤ M) (z : ℝ) :
    0 ≤ deriv (connectorRate K) z ∧ deriv (connectorRate K) z ≤ 1/8 := by
  have hKp : 0 < K := by linarith
  rw [(connectorRate_hasDerivAt K z).deriv]
  have hn : 0 ≤ deriv smoothTransition ((z-1)/K) := smoothTransition.monotone.deriv_nonneg
  have hu : deriv smoothTransition ((z-1)/K) ≤ M :=
    (le_abs_self _).trans (hbound _)
  constructor
  · positivity
  · calc
      _ ≤ (5/(2*K))*M := mul_le_mul_of_nonneg_left hu (by positivity)
      _ ≤ 1/8 := by
        rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0 < 2*K)]
        linarith

lemma connectorProfile_pos (K z : ℝ) : 0 < connectorProfile K z := exp_pos _
lemma connectorProfile_smooth (K : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (connectorProfile K) := by
  let r : SmoothScalar ℝ := ⟨connectorRate K,connectorRate_smooth K⟩
  exact ((smoothScalar_contDiff (smoothPrimitive r)).neg).exp

lemma connectorProfile_hasDerivAt (K z : ℝ) : HasDerivAt (connectorProfile K)
    (-connectorRate K z*connectorProfile K z) z := by
  have hr := (connectorRate_smooth K).continuous
  have h := intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable 0 z)
    (hr.stronglyMeasurableAtFilter _ _) hr.continuousAt
  change HasDerivAt (fun w => exp (-(∫ t in (0:ℝ)..w, connectorRate K t)))
    (-connectorRate K z*connectorProfile K z) z
  exact h.neg.exp.congr_deriv (g' := -connectorRate K z*connectorProfile K z)
    (by simp only [connectorProfile,Pi.neg_apply]; ring)

lemma connectorProfile_second (K z : ℝ) :
    deriv (deriv (connectorProfile K)) z =
      ((connectorRate K z)^2-deriv (connectorRate K) z)*connectorProfile K z := by
  have he : deriv (connectorProfile K) = fun z => -connectorRate K z*connectorProfile K z :=
    funext fun z => (connectorProfile_hasDerivAt K z).deriv
  rw [he]
  have h := (((connectorRate_smooth K).differentiable (by simp) z).hasDerivAt.neg).mul
    (connectorProfile_hasDerivAt K z)
  simp only [Pi.mul_def,Pi.neg_def] at h
  rw [h.deriv]
  ring

lemma connectorAngular_formula (K z : ℝ) : connectorAngular K z =
    (connectorRate K z)^2-deriv (connectorRate K) z := by
  rw [connectorAngular,connectorProfile_second,mul_div_cancel_right₀ _
    (connectorProfile_pos K z).ne']

lemma connectorAngular_bounds {M K : ℝ} (hM : 1 ≤ M) (hK : 20*M ≤ K)
    (hbound : ∀ x : ℝ, |deriv smoothTransition x| ≤ M) (z : ℝ) :
    1/8 ≤ connectorAngular K z ∧ connectorAngular K z ≤ 9 := by
  rw [connectorAngular_formula]
  obtain ⟨hl,hu⟩ := connectorRate_bounds K z
  obtain ⟨hdl,hdu⟩ := connectorRate_derivative_bounds hM hK hbound z
  constructor <;> nlinarith

lemma connectorProfile_le_one {K z : ℝ} (hz : 0 ≤ z) : connectorProfile K z ≤ 1 := by
  apply exp_le_one_iff.mpr
  have hn : 0 ≤ ∫ t in (0 : ℝ)..z, connectorRate K t :=
    intervalIntegral.integral_nonneg hz (fun t _ => le_trans (by norm_num) (connectorRate_bounds K t).1)
  exact neg_nonpos.mpr hn

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma crossingOn_smooth (L : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingOn L) := by
  exact smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).div_const L |>.add contDiff_const)
lemma crossingOff_smooth (L : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingOff L) := by
  exact contDiff_const.sub (smoothTransition.contDiff.comp
    (((contDiff_const.mul contDiff_id).div_const L).sub contDiff_const))
lemma crossingFirst_smooth (L : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingFirst L) := by
  exact (crossingOff_smooth L).mul ((contDiff_const.mul contDiff_id).exp)
lemma crossingSecond_smooth (L : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingSecond L) := by
  exact (crossingOn_smooth L).mul (contDiff_id.neg.exp)

lemma crossingOn_bounds (L z : ℝ) : 0 ≤ crossingOn L z ∧ crossingOn L z ≤ 1 :=
  ⟨smoothTransition.nonneg _,smoothTransition.le_one _⟩
lemma crossingOff_bounds (L z : ℝ) : 0 ≤ crossingOff L z ∧ crossingOff L z ≤ 1 := by
  constructor <;> dsimp [crossingOff]
  · linarith [smoothTransition.le_one (4*z/L-2)]
  · linarith [smoothTransition.nonneg (4*z/L-2)]

lemma crossingOn_eq_zero {L z : ℝ} (hL : 0 < L) (hz : z ≤ -3*L/4) :
    crossingOn L z = 0 := by
  apply smoothTransition.zero_of_nonpos
  have : 4*z/L ≤ -3 := (div_le_iff₀ hL).mpr (by linarith)
  linarith
lemma crossingOn_eq_one {L z : ℝ} (hL : 0 < L) (hz : -L/2 ≤ z) :
    crossingOn L z = 1 := by
  apply smoothTransition.one_of_one_le
  have : -2 ≤ 4*z/L := (le_div_iff₀ hL).mpr (by linarith)
  linarith
lemma crossingOff_eq_one {L z : ℝ} (hL : 0 < L) (hz : z ≤ L/2) :
    crossingOff L z = 1 := by
  have : 4*z/L ≤ 2 := (div_le_iff₀ hL).mpr (by linarith)
  rw [crossingOff,smoothTransition.zero_of_nonpos (by linarith),sub_zero]
lemma crossingOff_eq_zero {L z : ℝ} (hL : 0 < L) (hz : 3*L/4 ≤ z) :
    crossingOff L z = 0 := by
  have : 3 ≤ 4*z/L := (le_div_iff₀ hL).mpr (by linarith)
  rw [crossingOff,smoothTransition.one_of_one_le (by linarith),sub_self]

lemma crossingOn_hasDerivAt (L z : ℝ) : HasDerivAt (crossingOn L)
    ((4/L)*deriv smoothTransition (4*z/L+3)) z := by
  have h := ((smoothTransition.contDiff (n := ⊤)).differentiable (by simp) (4*z/L+3)).hasDerivAt
  change HasDerivAt (fun w => smoothTransition (4*w/L+3)) ((4/L)*deriv smoothTransition (4*z/L+3)) z
  exact (h.comp z (((hasDerivAt_id z).const_mul 4).div_const L |>.add_const 3)).congr_deriv
    (g' := (4/L)*deriv smoothTransition (4*z/L+3))
    (by simp only [mul_one]; ring)
lemma crossingOff_hasDerivAt (L z : ℝ) : HasDerivAt (crossingOff L)
    (-(4/L)*deriv smoothTransition (4*z/L-2)) z := by
  have h := ((smoothTransition.contDiff (n := ⊤)).differentiable (by simp) (4*z/L-2)).hasDerivAt
  change HasDerivAt (fun w => 1-smoothTransition (4*w/L-2)) (-(4/L)*deriv smoothTransition (4*z/L-2)) z
  exact ((h.comp z ((((hasDerivAt_id z).const_mul 4).div_const L).sub_const 2)).const_sub 1).congr_deriv
    (g' := -(4/L)*deriv smoothTransition (4*z/L-2))
    (by simp only [mul_one]; ring)

lemma deriv_crossingOn (L : ℝ) : deriv (crossingOn L) =
    fun z => (4/L)*deriv smoothTransition (4*z/L+3) :=
  funext fun z => (crossingOn_hasDerivAt L z).deriv
lemma deriv_crossingOff (L : ℝ) : deriv (crossingOff L) =
    fun z => -(4/L)*deriv smoothTransition (4*z/L-2) :=
  funext fun z => (crossingOff_hasDerivAt L z).deriv

lemma crossingOn_second (L z : ℝ) : deriv (deriv (crossingOn L)) z =
    (4/L)^2*deriv (deriv smoothTransition) (4*z/L+3) := by
  rw [deriv_crossingOn]
  have h := ((smooth_deriv_infty smoothTransition.contDiff).differentiable (by simp) (4*z/L+3)).hasDerivAt
  have hh := (h.comp z ((((hasDerivAt_id z).const_mul 4).div_const L).add_const 3)).const_mul (4/L)
  convert hh.deriv using 1 <;> simp only [Function.comp_def, id_eq, mul_one]
  ring
lemma crossingOff_second (L z : ℝ) : deriv (deriv (crossingOff L)) z =
    -(4/L)^2*deriv (deriv smoothTransition) (4*z/L-2) := by
  rw [deriv_crossingOff]
  have h := ((smooth_deriv_infty smoothTransition.contDiff).differentiable (by simp) (4*z/L-2)).hasDerivAt
  have hh := (h.comp z ((((hasDerivAt_id z).const_mul 4).div_const L).sub_const 2)).const_mul (-(4/L))
  convert hh.deriv using 1 <;> simp only [Function.comp_def, id_eq, mul_one]
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma connectorProfile_left {K z : ℝ} (hK : 0 < K) (hz : z ≤ 1) :
    connectorProfile K z = exp (-z/2) := by
  have hi : (∫ t in (0:ℝ)..z, connectorRate K t) = z/2 := by
    calc
      _ = ∫ _t in (0:ℝ)..z, (1/2:ℝ) := intervalIntegral.integral_congr (by
        intro t ht
        exact connectorRate_left hK ((le_max_iff.mp ht.2).elim (by intro h; linarith) (by intro h; linarith)))
      _ = _ := by simp; ring
  rw [connectorProfile,hi]
  congr 1
  ring

lemma cascadeProfile_smooth (L K : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (cascadeProfile L K) := by
  exact (((crossingOn_smooth L).comp ((contDiff_id.div_const 2).add contDiff_const)).mul
    (connectorProfile_smooth K)).mul ((crossingOff_smooth L).comp (contDiff_id.sub contDiff_const))

lemma cascadeProfile_zero_left {L K t : ℝ} (hL : 0 < L) (ht : t ≤ -7*L/2) :
    cascadeProfile L K t = 0 := by
  rw [cascadeProfile,crossingOn_eq_zero hL (show t/2+L ≤ -3*L/4 by linarith),zero_mul,zero_mul]
lemma cascadeProfile_zero_right {L K t : ℝ} (hL : 0 < L) (ht : K+2+7*L/4 ≤ t) :
    cascadeProfile L K t = 0 := by
  rw [cascadeProfile,crossingOff_eq_zero hL (show 3*L/4 ≤ t-(K+2+L) by linarith),mul_zero]

lemma cascadeProfile_compact {L K : ℝ} (hL : 0 < L) : HasCompactSupport (cascadeProfile L K) := by
  apply HasCompactSupport.intro (K := Icc (-7*L/2) (K+2+7*L/4)) isCompact_Icc
  intro t ht
  rw [mem_Icc,not_and_or,not_le,not_le] at ht
  rcases ht with ht | ht
  · exact cascadeProfile_zero_left hL ht.le
  · exact cascadeProfile_zero_right hL ht.le

lemma cascadeRatio_pos (L K : ℝ) : 0 < cascadeRatio L K :=
  mul_pos (exp_pos _) (connectorProfile_pos _ _)

lemma cascadeRatio_small {L K : ℝ} (hL : 1 ≤ L) (hK : 0 < K) :
    4*cascadeRatio L K < 1 := by
  have he : exp (-4*L) < 1/4 := by
    rw [neg_mul,exp_neg,one_div,inv_lt_inv₀ (exp_pos _) (by norm_num : (0:ℝ)<4)]
    have := add_one_le_exp (4*L)
    linarith
  have hc := connectorProfile_le_one (K := K) (z := K+2) (by linarith)
  have hq : cascadeRatio L K ≤ exp (-4*L) := by
    exact (mul_le_mul_of_nonneg_left hc (exp_pos _).le).trans_eq (mul_one _)
  linarith

lemma cascade_length_positive {L K : ℝ} (hL : 0 < L) (hK : 0 < K) :
    0 < cascadeLength L K := by unfold cascadeLength; linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingHxx
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

section
open Real

lemma crossing_coefficients_small {D J R l m ε : ℝ}
    (hD : D ≠ 0) (hl : l ≠ 0) (hm : m ≠ 0)
    (hα : |R / (D*l^2)| ≤ ε) (hβ : |J/D| ≤ 1) (hr : |l/m| ≤ 2)
    (x y : ℝ) :
    |crossingHxx D J R l m x y| ≤ 3*ε ∧
      |crossingHxy D R l m x y| ≤ 4*ε := by
  have he : 0 ≤ ε := (abs_nonneg _).trans hα
  have hs (t : ℝ) : |sin t| ≤ 1 := abs_sin_le_one t
  have hc (t : ℝ) : |cos t| ≤ 1 := abs_cos_le_one t
  have hxx : crossingHxx D J R l m x y =
      (R/(D*l^2)) * (cos (l*x)*cos (m*y) - 2*(J/D)*sin (m*y)^2) := by
    unfold crossingHxx
    field_simp
  have hxy : crossingHxy D R l m x y =
      2*(R/(D*l^2))*(l/m)*(sin (l*x)*sin (m*y)) := by
    unfold crossingHxy
    field_simp
  have hp (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a*b| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg a, abs_nonneg b]
  have hsin2 : |sin (m*y)^2| ≤ 1 := by
    simpa only [pow_two] using hp _ _ (hs (m*y)) (hs (m*y))
  constructor
  · rw [hxx, abs_mul]
    have h1 := hp _ _ (hc (l*x)) (hc (m*y))
    have h2 : |2*(J/D)*sin (m*y)^2| ≤ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
      nlinarith [abs_nonneg (J/D), abs_nonneg (sin (m*y)^2)]
    have hh := abs_sub (cos (l*x)*cos (m*y)) (2*(J/D)*sin (m*y)^2)
    nlinarith [abs_nonneg (R/(D*l^2))]
  · rw [hxy, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hh := hp _ _ (hs (l*x)) (hs (m*y))
    have hprod : |R/(D*l^2)| * |l/m| ≤ 2*ε := by
      nlinarith [abs_nonneg (R/(D*l^2)), abs_nonneg (l/m)]
    nlinarith [abs_nonneg (R/(D*l^2)), abs_nonneg (l/m),
      abs_nonneg (sin (l*x)*sin (m*y)), mul_nonneg (abs_nonneg (R/(D*l^2))) (abs_nonneg (l/m))]

lemma crossing_quadratic_ellipticity {a b h k ε : ℝ}
    (ha : 1/4 ≤ a) (hb : 1/4 ≤ b) (ha' : a ≤ 9) (hb' : b ≤ 9)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1/56) (hh : |h| ≤ 3*ε) (hk : |k| ≤ 4*ε)
    (x y : ℝ) :
    (1/8)*(x^2+y^2) ≤ (a+h)*x^2+2*k*x*y+b*y^2 ∧
      (a+h)*x^2+2*k*x*y+b*y^2 ≤ 10*(x^2+y^2) := by
  have hh' := (abs_le.mp hh)
  have hk' := (abs_le.mp hk)
  have hx : 0 ≤ x^2 := sq_nonneg x
  have hy : 0 ≤ y^2 := sq_nonneg y
  have hcross : |2*k*x*y| ≤ 4*ε*(x^2+y^2) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hs : 2*|x| * |y| ≤ x^2+y^2 := by
      nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
    have hkxy := mul_le_mul_of_nonneg_right hk (mul_nonneg (abs_nonneg x) (abs_nonneg y))
    have hexy := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4*ε)
    nlinarith
  have hcross' := abs_le.mp hcross
  have hal := mul_le_mul_of_nonneg_right ha hx
  have hbl := mul_le_mul_of_nonneg_right hb hy
  have hau := mul_le_mul_of_nonneg_right ha' hx
  have hbu := mul_le_mul_of_nonneg_right hb' hy
  have hhl := mul_le_mul_of_nonneg_right hh'.1 hx
  have hhu := mul_le_mul_of_nonneg_right hh'.2 hx
  have heu := mul_le_mul_of_nonneg_right hε' (add_nonneg hx hy)
  have hey := mul_nonneg hε hy
  constructor <;> nlinarith

end

open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ScaledSmoothSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma compact_iteratedFDeriv_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  obtain ⟨C,hC⟩ := ((hfc.iteratedFDeriv n).isCompact_range
    (((contDiff_infty.mp hf) n).continuous_iteratedFDeriv le_rfl)).isBounded.exists_norm_le
  refine ⟨max C 0,le_max_right _ _,fun x => ?_⟩
  exact (hC _ (mem_range_self x)).trans (le_max_left _ _)

lemma cascadeMother_smooth (L K : ℝ) (axis : Fin 3) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cascadeMother L K axis) := by
  exact ((cascadeProfile_smooth L K).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).contDiff).mul
    (Real.contDiff_cos.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) axis).contDiff)

lemma cascadeMother_iterated_bound {L K : ℝ} (hL : 0 < L) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (axis : Fin 3) (x : Coord3),
      ‖iteratedFDeriv ℝ n (cascadeMother L K axis) x‖ ≤ C := by
  have hp : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖iteratedFDeriv ℝ i (cascadeProfile L K) x‖ ≤ C :=
    compact_iteratedFDeriv_bound (cascadeProfile_smooth L K) (cascadeProfile_compact hL)
  choose C hC0 hC using hp
  let P : Fin 3 → Coord3 →L[ℝ] ℝ := fun i => ContinuousLinearMap.proj i
  let b : Fin 3 → ℝ := fun axis => ∑ i ∈ Finset.range (n+1),
    (n.choose i : ℝ)*(C i*‖P 0‖^i)*(1*‖P axis‖^(n-i))
  refine ⟨∑ axis, b axis,Finset.sum_nonneg (fun a _ => ?_),fun axis x => ?_⟩
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC0 i) (by positivity))) (by positivity))
  · apply le_trans (norm_iteratedFDeriv_mul_le
      ((cascadeProfile_smooth L K).comp (P 0).contDiff)
      (Real.contDiff_cos.comp (P axis).contDiff) x (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
    apply le_trans (b := b axis)
    · apply Finset.sum_le_sum
      intro i hi
      have h₁ := linear_comp_iterated_bound (P 0) (cascadeProfile_smooth L K) (hC i) x
      have h₂ := linear_comp_iterated_bound (P axis) Real.contDiff_cos
        (fun z => by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
          (sin_cos_iterated_bound (n-i) z).2) x
      exact mul_le_mul (mul_le_mul_of_nonneg_left h₁ (by positivity)) h₂
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC0 i) (by positivity)))
    · change b axis ≤ ∑ a, b a
      apply Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun i _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC0 i) (by positivity))) (by positivity)))
        (Finset.mem_univ axis)

lemma scaled_iterated_bound {f : Coord3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    {order : ℕ} {C : ℝ} (hC : ∀ x, ‖iteratedFDeriv ℝ order f x‖ ≤ C) (a p : ℝ) (b x : Coord3) :
    ‖iteratedFDeriv ℝ order (fun y => a*f (p • (y-b))) x‖ ≤ |a| * C * |p|^order := by
  let g : Coord3 →L[ℝ] Coord3 := p • ContinuousLinearMap.id ℝ Coord3
  have he : (fun y => a*f (p • (y-b))) = a • (fun y => (f ∘ g) (y-b)) := by rfl
  have hfb : ContDiff ℝ order (fun y => (f ∘ g) (y-b)) :=
    ((contDiff_infty.mp hf) order).comp (g.contDiff.comp (contDiff_id.sub contDiff_const))
  rw [he,iteratedFDeriv_const_smul_apply hfb.contDiffAt,norm_smul,iteratedFDeriv_comp_sub]
  have hh := linear_comp_iterated_bound g hf hC (x-b)
  have hg : ‖g‖ = |p| := by simp [g,norm_smul,ContinuousLinearMap.norm_id,Real.norm_eq_abs]
  rw [hg] at hh
  simpa only [Real.norm_eq_abs,mul_assoc] using mul_le_mul_of_nonneg_left hh (abs_nonneg a)

theorem geometric_scaled_C2 {f : ℕ → Coord3 → ℝ}
    (hf : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j x, ‖iteratedFDeriv ℝ n (f j) x‖ ≤ C)
    {q : ℝ} (hq : 0 ≤ q) (hqsmall : 4*q<1) (A k : ℝ) (center : ℕ → Coord3) :
    ContDiff ℝ 2 (fun x => ∑' j : ℕ, (A*q^j)*f j ((k*2^j) • (x-center j))) := by
  choose C hC0 hC using hb
  let v : ℕ → ℕ → ℝ := fun n j => |A| * C n * |k|^n*(q*(2:ℝ)^n)^j
  apply contDiff_tsum (v := v)
  · intro j
    exact contDiff_const.mul (((contDiff_infty.mp (hf j)) 2).comp
      ((contDiff_id.sub contDiff_const).const_smul (k*2^j)))
  · intro n hn
    have hn' : n ≤ 2 := by exact_mod_cast hn
    have hc : ‖q*(2:ℝ)^n‖ < 1 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hp : (2:ℝ)^n ≤ 4 := by
        calc (2:ℝ)^n ≤ 2^2 := pow_le_pow_right₀ (by norm_num) hn'
             _ = 4 := by norm_num
      nlinarith
    exact (summable_geometric_of_norm_lt_one hc).mul_left _
  · intro n j x hn
    have hh := scaled_iterated_bound (hf j) (hC n j) (A*q^j) (k*2^j) (center j) x
    apply hh.trans_eq
    dsimp [v]
    rw [abs_mul,abs_pow,abs_of_nonneg hq,abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<2),
      mul_pow,mul_pow,←pow_mul,←pow_mul]
    ring

lemma BoundedSmooth.of_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hc : HasCompactSupport f) : BoundedSmooth f :=
  ⟨hf,compact_iteratedFDeriv_bound hf hc⟩

lemma BoundedSmooth.add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x => f x+g x) := by
  refine ⟨hf.1.add hg.1,fun n => ?_⟩
  obtain ⟨C,hC,hCf⟩ := hf.2 n
  obtain ⟨D,hD,hDg⟩ := hg.2 n
  refine ⟨C+D,add_nonneg hC hD,fun x => ?_⟩
  change ‖iteratedFDeriv ℝ n (f+g) x‖ ≤ C+D
  rw [iteratedFDeriv_add_apply (hf.1.of_le (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))).contDiffAt
    (hg.1.of_le (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hCf x) (hDg x))

lemma BoundedSmooth.smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : BoundedSmooth f) (a : ℝ) : BoundedSmooth (fun x => a*f x) := by
  refine ⟨contDiff_const.mul hf.1,fun n => ?_⟩
  obtain ⟨C,hC,hCf⟩ := hf.2 n
  refine ⟨|a| * C,mul_nonneg (abs_nonneg _) hC,fun x => ?_⟩
  change ‖iteratedFDeriv ℝ n (a • f) x‖ ≤ |a| * C
  rw [iteratedFDeriv_const_smul_apply ((contDiff_infty.mp hf.1) n).contDiffAt,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hCf x) (abs_nonneg _)

lemma BoundedSmooth.sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x => f x-g x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hf.add (hg.smul (-1))

lemma BoundedSmooth.mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x => f x*g x) := by
  choose C hC hCf using hf.2
  choose D hD hDg using hg.2
  refine ⟨hf.1.mul hg.1,fun n => ⟨∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*C i*D (n-i),?_,?_⟩⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (hD _)
  · intro x
    apply (norm_iteratedFDeriv_mul_le hf.1 hg.1 x
      (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))).trans
    exact Finset.sum_le_sum fun i _ => mul_le_mul
      (mul_le_mul_of_nonneg_left (hCf i x) (Nat.cast_nonneg _)) (hDg (n-i) x)
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC i))

lemma BoundedSmooth.comp_linear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → ℝ} (hf : BoundedSmooth f)
    (g : F →L[ℝ] E) : BoundedSmooth (f ∘ g) := by
  refine ⟨hf.1.comp g.contDiff,fun n => ?_⟩
  obtain ⟨C,hC,hCf⟩ := hf.2 n
  exact ⟨C*‖g‖^n,mul_nonneg hC (by positivity),linear_comp_iterated_bound g hf.1 hCf⟩

lemma BoundedSmooth.translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : BoundedSmooth f) (b : E) : BoundedSmooth (fun x => f (x-b)) := by
  refine ⟨hf.1.comp (contDiff_id.sub contDiff_const),fun n => ?_⟩
  obtain ⟨C,hC,hCf⟩ := hf.2 n
  refine ⟨C,hC,fun x => ?_⟩
  rw [iteratedFDeriv_comp_sub]
  exact hCf (x-b)

lemma sin_boundedSmooth : BoundedSmooth Real.sin :=
  ⟨Real.contDiff_sin,fun n => ⟨1,by norm_num,fun x => by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using (sin_cos_iterated_bound n x).1⟩⟩
lemma cos_boundedSmooth : BoundedSmooth Real.cos :=
  ⟨Real.contDiff_cos,fun n => ⟨1,by norm_num,fun x => by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using (sin_cos_iterated_bound n x).2⟩⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma cascadePhase_zero (D k t : ℝ) : cascadePhase D k 0 t = k*t := by
  simp [cascadePhase]

lemma cascadePhase_succ (D k t : ℝ) (j : ℕ) :
    cascadePhase D k (j+1) t = 2*(cascadePhase D k j t-D) := by
  unfold cascadePhase
  rw [pow_succ]
  ring

lemma cascadePhase_antitone {D k t : ℝ} (ht : k*t ≤ 2*D) :
    Antitone (fun j => cascadePhase D k j t) := by
  apply antitone_nat_of_succ_le
  intro j
  have hp : 0 ≤ (2:ℝ)^j := by positivity
  rw [cascadePhase_succ]
  have : cascadePhase D k j t ≤ 2*D := by
    unfold cascadePhase
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hp (by linarith : k*t-2*D≤0)]
  linarith

lemma cascadeProfile_terminal {L K k t : ℝ} (hL : 0 < L) (hK : 0 < K)
    (ht : 2*cascadeLength L K ≤ k*t) (j : ℕ) :
    cascadeProfile L K (cascadePhase (cascadeLength L K) k j t) = 0 := by
  apply cascadeProfile_zero_right hL
  have hp : 0 ≤ (2:ℝ)^j*(k*t-2*cascadeLength L K) :=
    mul_nonneg (by positivity) (by linarith)
  unfold cascadePhase cascadeLength at *
  linarith

lemma cascadeAxis_ne_zero (j : ℕ) : cascadeAxis j ≠ 0 := by
  unfold cascadeAxis
  split <;> decide

lemma cascadeAxis_succ (j : ℕ) : cascadeAxis (j+1) = if Even j then 2 else 1 := by
  simp only [cascadeAxis,Nat.even_add_one]
  split <;> simp_all

lemma cascade_dilation_time {k : ℝ} (hk : k ≠ 0) (D : ℝ) (j : ℕ) (x : Coord3) :
    ((k*2^j) • (x-cascadeCenter D k j)) 0 = cascadePhase D k j (x 0) := by
  simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,cascadeCenter,Pi.single_eq_same,cascadePhase]
  field_simp
  ring

lemma cascade_dilation_angular (D k : ℝ) (j : ℕ) (x : Coord3) :
    ((k*2^j) • (x-cascadeCenter D k j)) (cascadeAxis j) = k*2^j*x (cascadeAxis j) := by
  simp [cascadeCenter,Pi.single_eq_of_ne (cascadeAxis_ne_zero j)]

lemma cascadeTerm_scaled {k : ℝ} (hk : k ≠ 0) (L K A : ℝ) (j : ℕ) (x : Coord3) :
    cascadeTerm L K k A j x = (A*cascadeRatio L K^j)*
      cascadeMother L K (cascadeAxis j) ((k*2^j) • (x-cascadeCenter (cascadeLength L K) k j)) := by
  rw [cascadeMother,cascade_dilation_time hk,cascade_dilation_angular]
  unfold cascadeTerm
  ring

theorem cascadeValue_C2 {L K k : ℝ} (hL : 1 ≤ L) (hK : 0 < K) (hk : k ≠ 0) (A : ℝ) :
    ContDiff ℝ 2 (cascadeValue L K k A) := by
  have hh := geometric_scaled_C2
    (f := fun j => cascadeMother L K (cascadeAxis j))
    (fun _ => cascadeMother_smooth _ _ _)
    (fun n => by
      obtain ⟨C,hC,hb⟩ := cascadeMother_iterated_bound (lt_of_lt_of_le (by norm_num) hL) n
      exact ⟨C,hC,fun j x => hb (cascadeAxis j) x⟩)
    (cascadeRatio_pos L K).le (cascadeRatio_small hL hK) A k
    (cascadeCenter (cascadeLength L K) k)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact tsum_congr fun j => cascadeTerm_scaled hk L K A j x

lemma cascadeValue_terminal {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (A : ℝ)
    (x : Coord3) (hx : 2*cascadeLength L K ≤ k*x 0) : cascadeValue L K k A x = 0 := by
  change (∑' j : ℕ, cascadeTerm L K k A j x) = 0
  have h : ∀ j, cascadeTerm L K k A j x = 0 := by
    intro j
    rw [cascadeTerm,cascadeProfile_terminal hL hK hx,mul_zero,zero_mul]
  simp only [h,tsum_zero]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma cutoff_exp_hasDerivAt {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (a z : ℝ) :
    HasDerivAt (fun z => χ z * exp (-a*z))
      ((deriv χ z-a*χ z)*exp (-a*z)) z := by
  have hd := (hχ.differentiable (by simp) z).hasDerivAt
  have he := ((hasDerivAt_id z).const_mul (-a)).exp
  exact (hd.mul he).congr_deriv
    (g' := (deriv χ z-a*χ z)*exp (-a*z)) (by simp only [id_eq,mul_one]; ring)

lemma cutoff_exp_residual {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (a z : ℝ) :
    deriv (deriv (fun z => χ z * exp (-a*z))) z - a^2*(χ z * exp (-a*z)) =
      (deriv (deriv χ) z-2*a*deriv χ z)*exp (-a*z) := by
  have he : deriv (fun z => χ z * exp (-a*z)) =
      fun z => (deriv χ z-a*χ z)*exp (-a*z) :=
    funext fun z => (cutoff_exp_hasDerivAt hχ a z).deriv
  rw [he]
  have hd := ((smooth_deriv_infty hχ).differentiable (by simp) z).hasDerivAt
  have hd₁ := (hχ.differentiable (by simp) z).hasDerivAt
  have hd₂ := ((hd.sub (hd₁.const_mul a)).mul (((hasDerivAt_id z).const_mul (-a)).exp))
  simp only [Pi.mul_def,Pi.sub_def,id_eq,mul_one] at hd₂
  rw [hd₂.deriv]
  ring

lemma crossing_cutoff_derivative_bounds {M L : ℝ} (hM0 : 1 ≤ M) (hL : 1 ≤ L)
    (hM : ∀ x : ℝ, |deriv smoothTransition x| ≤ M ∧
      |deriv (deriv smoothTransition) x| ≤ M) (z : ℝ) :
    |deriv (crossingOn L) z| ≤ 4*M ∧
    |deriv (deriv (crossingOn L)) z| ≤ 16*M ∧
    |deriv (crossingOff L) z| ≤ 4*M ∧
    |deriv (deriv (crossingOff L)) z| ≤ 16*M := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hq : |4/L| ≤ 4 := by
    rw [abs_of_pos (div_pos (by norm_num) hLp)]
    exact (div_le_iff₀ hLp).mpr (by linarith)
  have hq₂ : |(4/L)^2| ≤ 16 := by
    rw [abs_pow]
    nlinarith [abs_nonneg (4/L)]
  rw [crossingOn_second,crossingOff_second,deriv_crossingOn,deriv_crossingOff]
  simp only [abs_mul,abs_neg]
  constructor
  · rw [mul_comm, mul_comm 4 M]
    exact mul_le_mul (hM _).1 hq (abs_nonneg _) (zero_le_one.trans hM0)
  · exact ⟨mul_le_mul hq₂ (hM _).2 (abs_nonneg _) (by norm_num),
      mul_le_mul hq (hM _).1 (abs_nonneg _) (by norm_num),
      mul_le_mul hq₂ (hM _).2 (abs_nonneg _) (by norm_num)⟩

lemma crossingResidualFirst_formula (L z : ℝ) :
    crossingResidualFirst L z =
      (deriv (deriv (crossingOff L)) z-6*deriv (crossingOff L) z)*exp (-3*z) := by
  unfold crossingResidualFirst crossingFirst
  simpa only [show (3:ℝ)^2=9 by norm_num,show (2:ℝ)*3=6 by norm_num] using
    cutoff_exp_residual (crossingOff_smooth L) 3 z
lemma crossingResidualSecond_formula (L z : ℝ) :
    crossingResidualSecond L z =
      (deriv (deriv (crossingOn L)) z-2*deriv (crossingOn L) z)*exp (-z) := by
  unfold crossingResidualSecond crossingSecond
  simpa only [one_pow,one_mul,mul_one,neg_one_mul] using
    cutoff_exp_residual (crossingOn_smooth L) 1 z

lemma crossingResidualFirst_normalized (L z : ℝ) :
    crossingResidualFirst L z / exp (-z) =
      (deriv (deriv (crossingOff L)) z-6*deriv (crossingOff L) z)*exp (-2*z) := by
  rw [crossingResidualFirst_formula,mul_div_assoc,←exp_sub]
  congr 2
  ring
lemma crossingResidualSecond_normalized (L z : ℝ) :
    crossingResidualSecond L z / exp (-3*z) =
      (deriv (deriv (crossingOn L)) z-2*deriv (crossingOn L) z)*exp (2*z) := by
  rw [crossingResidualSecond_formula,mul_div_assoc,←exp_sub]
  congr 2
  ring

lemma crossingResidualFirst_zero {L z : ℝ} (hL : 0 < L) (hz : z < L/2) :
    crossingResidualFirst L z = 0 := by
  have hu : 4*z/L-2 < 0 := by
    have : 4*z/L < 2 := (div_lt_iff₀ hL).mpr (by linarith)
    linarith
  rw [crossingResidualFirst_formula,crossingOff_second]
  simp only [deriv_crossingOff,
    (smoothTransition_flat_left hu).1,(smoothTransition_flat_left hu).2]
  ring
lemma crossingResidualSecond_zero {L z : ℝ} (hL : 0 < L) (hz : -L/2 < z) :
    crossingResidualSecond L z = 0 := by
  have hu : 1 < 4*z/L+3 := by
    have : -2 < 4*z/L := (lt_div_iff₀ hL).mpr (by linarith)
    linarith
  rw [crossingResidualSecond_formula,crossingOn_second]
  simp only [deriv_crossingOn,
    (smoothTransition_flat_right hu).1,(smoothTransition_flat_right hu).2]
  ring

lemma crossing_residual_bounds {M L : ℝ} (hM0 : 1 ≤ M) (hL : 1 ≤ L)
    (hM : ∀ x : ℝ, |deriv smoothTransition x| ≤ M ∧
      |deriv (deriv smoothTransition) x| ≤ M) (z : ℝ) :
    |crossingResidualFirst L z / exp (-z)| ≤ 40*M*exp (-L) ∧
    |crossingResidualSecond L z / exp (-3*z)| ≤ 40*M*exp (-L) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hMp : 0 ≤ M := le_trans (by norm_num) hM0
  obtain ⟨hon₁,hon₂,hoff₁,hoff₂⟩ := crossing_cutoff_derivative_bounds hM0 hL hM z
  constructor
  · by_cases hz : z < L/2
    · rw [crossingResidualFirst_zero hLp hz,zero_div,abs_zero]
      positivity
    · rw [crossingResidualFirst_normalized,abs_mul,abs_of_pos (exp_pos _)]
      have he : exp (-2*z) ≤ exp (-L) := exp_le_exp.mpr (by linarith)
      have hr : |deriv (deriv (crossingOff L)) z-6*deriv (crossingOff L) z| ≤ 40*M := by
        have := abs_sub (deriv (deriv (crossingOff L)) z) (6*deriv (crossingOff L) z)
        rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<6)] at this
        linarith
      exact mul_le_mul hr he (exp_pos _).le (by positivity)
  · by_cases hz : -L/2 < z
    · rw [crossingResidualSecond_zero hLp hz,zero_div,abs_zero]
      positivity
    · rw [crossingResidualSecond_normalized,abs_mul,abs_of_pos (exp_pos _)]
      have he : exp (2*z) ≤ exp (-L) := exp_le_exp.mpr (by linarith)
      have hr : |deriv (deriv (crossingOn L)) z-2*deriv (crossingOn L) z| ≤ 40*M := by
        have := abs_sub (deriv (deriv (crossingOn L)) z) (2*deriv (crossingOn L) z)
        rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at this
        linarith
      exact mul_le_mul hr he (exp_pos _).le (by positivity)

lemma crossing_mode_ratios {L z : ℝ} :
    (z ≤ 0 → |crossingSecond L z / exp (-3*z)| ≤ 1) ∧
    (0 ≤ z → |crossingFirst L z / exp (-z)| ≤ 1) := by
  constructor
  · intro hz
    rw [crossingSecond,mul_div_assoc,←exp_sub,abs_mul,
      abs_of_nonneg (crossingOn_bounds L z).1,abs_of_pos (exp_pos _)]
    have he : exp (-z- -3*z) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    exact (mul_le_mul_of_nonneg_left he (crossingOn_bounds L z).1).trans
      (by simpa using (crossingOn_bounds L z).2)
  · intro hz
    rw [crossingFirst,mul_div_assoc,←exp_sub,abs_mul,
      abs_of_nonneg (crossingOff_bounds L z).1,abs_of_pos (exp_pos _)]
    have he : exp (-3*z- -z) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    exact (mul_le_mul_of_nonneg_left he (crossingOff_bounds L z).1).trans
      (by simpa using (crossingOff_bounds L z).2)

lemma exists_small_crossing_scale {M : ℝ} (hM : 1 ≤ M) :
    ∃ L : ℝ, 1 ≤ L ∧ 40*M*exp (-L) ≤ 1/56 := by
  refine ⟨2240*M+1,by linarith,?_⟩
  rw [exp_neg,←div_eq_mul_inv,div_le_iff₀ (exp_pos _)]
  have := add_one_le_exp (2240*M+1)
  linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeStreams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma crossingResidualFirst_smooth (L : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingResidualFirst L) :=
  (smooth_deriv_infty (smooth_deriv_infty (crossingFirst_smooth L))).sub
    (contDiff_const.mul (crossingFirst_smooth L))
lemma crossingResidualSecond_smooth (L : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingResidualSecond L) :=
  (smooth_deriv_infty (smooth_deriv_infty (crossingSecond_smooth L))).sub (crossingSecond_smooth L)

lemma crossingResidualFirst_zero_right {L z : ℝ} (hL : 0 < L) (hz : 3*L/4 < z) :
    crossingResidualFirst L z = 0 := by
  have hu : 1 < 4*z/L-2 := by
    have : 3 < 4*z/L := (lt_div_iff₀ hL).mpr (by linarith)
    linarith
  rw [crossingResidualFirst_formula,crossingOff_second]
  simp only [deriv_crossingOff,(smoothTransition_flat_right hu).1,(smoothTransition_flat_right hu).2]
  ring
lemma crossingResidualSecond_zero_left {L z : ℝ} (hL : 0 < L) (hz : z < -3*L/4) :
    crossingResidualSecond L z = 0 := by
  have hu : 4*z/L+3 < 0 := by
    have : 4*z/L < -3 := (div_lt_iff₀ hL).mpr (by linarith)
    linarith
  rw [crossingResidualSecond_formula,crossingOn_second]
  simp only [deriv_crossingOn,(smoothTransition_flat_left hu).1,(smoothTransition_flat_left hu).2]
  ring

lemma crossingResidualFirst_compact {L : ℝ} (hL : 0 < L) : HasCompactSupport (crossingResidualFirst L) := by
  apply HasCompactSupport.intro (K := Icc (L/2) (3*L/4)) isCompact_Icc
  intro z hz
  simp only [mem_Icc,not_and_or,not_le] at hz
  exact hz.elim (crossingResidualFirst_zero hL) (crossingResidualFirst_zero_right hL)
lemma crossingResidualSecond_compact {L : ℝ} (hL : 0 < L) : HasCompactSupport (crossingResidualSecond L) := by
  apply HasCompactSupport.intro (K := Icc (-3*L/4) (-L/2)) isCompact_Icc
  intro z hz
  simp only [mem_Icc,not_and_or,not_le] at hz
  exact hz.elim (crossingResidualSecond_zero_left hL) (crossingResidualSecond_zero hL)

lemma cascadeBaseStream_bounded {L K : ℝ} (hL : 0 < L) (a : Fin 3) :
    BoundedSmooth (cascadeBaseStream L K a) := by
  let P : Fin 3 → Coord3 →L[ℝ] ℝ := fun i => ContinuousLinearMap.proj i
  exact ((BoundedSmooth.of_compact (smooth_deriv_infty (cascadeProfile_smooth L K))
    (cascadeProfile_compact hL).deriv).comp_linear (P 0)).mul
    (sin_boundedSmooth.comp_linear (P a))

lemma cascadeCrossStream_bounded {L K : ℝ} (hL : 0 < L) (a b : Fin 3) :
    BoundedSmooth (cascadeCrossStream L K a b) := by
  let P : Fin 3 → Coord3 →L[ℝ] ℝ := fun i => ContinuousLinearMap.proj i
  have hf := (((BoundedSmooth.of_compact (crossingResidualFirst_smooth L)
    (crossingResidualFirst_compact hL)).translate (K+2+L)).comp_linear (P 0)).smul (1/4)
  have hg := (((BoundedSmooth.of_compact (crossingResidualSecond_smooth L)
    (crossingResidualSecond_compact hL)).translate (K+2+L)).comp_linear (P 0)).smul (1/2)
  have hs₁ := sin_boundedSmooth.comp_linear (4 • P b)
  have hs₂ := sin_boundedSmooth.comp_linear (2 • P b)
  have hsa := sin_boundedSmooth.comp_linear (P a)
  have hca := cos_boundedSmooth.comp_linear (P a)
  convert (((hf.mul hs₁).mul hsa).sub (((hg.mul hca).mul hsa).mul hs₂)).smul
    (connectorProfile K (K+2)*exp (-3*L)) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [cascadeCrossStream,Function.comp_def,smul_apply,P,
    ContinuousLinearMap.proj_apply]
  ring_nf

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AntisymmetricFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma direction_C1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (v : E) : ContDiff ℝ 1 (direction v f) := by
  exact (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

lemma boundedSmooth_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    BoundedSmooth (fun _ : E => (0:ℝ)) :=
  BoundedSmooth.of_compact contDiff_const (HasCompactSupport.intro isCompact_empty (fun _ _ => rfl))

lemma geometric_finite_C2 {ι : Type*} [Fintype ι] {f : ι → Coord3 → ℝ}
    (hf : ∀ i, BoundedSmooth (f i)) (select : ℕ → ι)
    {q : ℝ} (hq : 0 ≤ q) (hqsmall : 4*q<1) (A k : ℝ) (center : ℕ → Coord3) :
    ContDiff ℝ 2 (fun x => ∑' j : ℕ, (A*q^j)*f (select j) ((k*2^j) • (x-center j))) := by
  apply geometric_scaled_C2 (fun j => (hf (select j)).1) _ hq hqsmall A k center
  intro n
  choose C hC hb using fun i => (hf i).2 n
  refine ⟨∑ i, C i,Finset.sum_nonneg (fun i _ => hC i),fun j x => ?_⟩
  exact (hb (select j) x).trans (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ _))

lemma cascadePotentialMother_bounded {L K : ℝ} (hL : 0 < L) (a b i j : Fin 3) :
    BoundedSmooth (cascadePotentialMother L K a b i j) := by
  unfold cascadePotentialMother
  have hb := cascadeBaseStream_bounded (K := K) hL a
  have hc := cascadeCrossStream_bounded (K := K) hL a b
  apply BoundedSmooth.sub <;> apply BoundedSmooth.add
  all_goals split <;> first | exact hb | exact hc | exact boundedSmooth_zero

lemma cascadePotential_C2 {L K : ℝ} (hL : 1 ≤ L) (hK : 0 < K) (k A : ℝ) (i j : Fin 3) :
    ContDiff ℝ 2 (cascadePotential L K k A i j) := by
  exact geometric_finite_C2
    (f := fun ab : Fin 3 × Fin 3 => cascadePotentialMother L K ab.1 ab.2 i j)
    (fun ab => cascadePotentialMother_bounded (lt_of_lt_of_le (by norm_num) hL) ab.1 ab.2 i j)
    (fun n => (cascadeAxis n,cascadeAxis (n+1)))
    (cascadeRatio_pos L K).le (cascadeRatio_small hL hK) A k
    (cascadeCenter (cascadeLength L K) k)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CrossingBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma crossing_corrections_left {L z : ℝ} (hL : 0 < L) (hz : z ≤ 0) (x y : ℝ) :
    crossingYY L z x y = 1/4 ∧
    crossingXY L z x y = crossingHxy (exp (-3*z)) (crossingResidualSecond L z) 1 2 x y := by
  have hr := crossingResidualFirst_zero hL (show z < L/2 by linarith)
  simp [crossingYY,crossingXY,hr,crossingHxx,crossingHxy]
lemma crossing_corrections_right {L z : ℝ} (hL : 0 < L) (hz : 0 ≤ z) (x y : ℝ) :
    crossingXX L z x y = 9 ∧
    crossingXY L z x y = crossingHxy (exp (-z)) (crossingResidualFirst L z) 2 1 y x := by
  have hr := crossingResidualSecond_zero hL (show -L/2 < z by linarith)
  simp [crossingXX,crossingXY,hr,crossingHxx,crossingHxy]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma cascadeProfile_deriv_zero_left {L K t : ℝ} (hL : 0 < L) (ht : t <  -7*L/2) :
    deriv (cascadeProfile L K) t = 0 := by
  have he : cascadeProfile L K =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with y hy
    exact cascadeProfile_zero_left hL hy.le
  simpa using he.deriv_eq
lemma cascadeProfile_deriv_zero_right {L K t : ℝ} (hL : 0 < L) (ht : K+2+7*L/4 < t) :
    deriv (cascadeProfile L K) t = 0 := by
  have he : cascadeProfile L K =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with y hy
    exact cascadeProfile_zero_right hL hy.le
  simpa using he.deriv_eq

lemma cascadeBaseStream_zero {L K : ℝ} (hL : 0 < L) (a : Fin 3) (x : Coord3)
    (ht : x 0 <  -7*L/2 ∨ K+2+7*L/4 < x 0) : cascadeBaseStream L K a x = 0 := by
  have hd : deriv (cascadeProfile L K) (x 0) = 0 :=
    ht.elim (cascadeProfile_deriv_zero_left hL) (cascadeProfile_deriv_zero_right hL)
  simp [cascadeBaseStream,hd]

lemma cascadeCrossStream_zero_left {L K : ℝ} (hL : 0 < L) (a b : Fin 3) (x : Coord3)
    (ht : x 0 < K+2+L/4) : cascadeCrossStream L K a b x = 0 := by
  have hf := crossingResidualFirst_zero hL (show x 0-(K+2+L) < L/2 by linarith)
  have hg := crossingResidualSecond_zero_left hL (show x 0-(K+2+L) <  -3*L/4 by linarith)
  simp [cascadeCrossStream,hf,hg]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CascadeStageCurl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma cascadeAxis_ne_succ (m : ℕ) : cascadeAxis m ≠ cascadeAxis (m+1) := by
  rw [cascadeAxis_succ]
  unfold cascadeAxis
  split <;> decide

lemma wedgePotential_as_mul (a b i j : Fin 3) (H : Coord3 → ℝ) (x : Coord3) :
    wedgePotential a b H i j x =
      ((if i=a ∧ j=b then (1:ℝ) else 0)-(if j=a ∧ i=b then (1:ℝ) else 0))*H x := by
  unfold wedgePotential
  split <;> split <;> ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma crossingTensor_mulVec (L : ℝ) (a b : Fin 3) (x v : Coord3) (i : Fin 3) :
    (crossingTensor L a b x *ᵥ v) i =
      (if i=0 then v 0 else 0) +
      (if i=a then crossingXX L (x 0) (x a) (x b)*v a+crossingXY L (x 0) (x a) (x b)*v b else 0) +
      (if i=b then crossingXY L (x 0) (x a) (x b)*v a+crossingYY L (x 0) (x a) (x b)*v b else 0) := by
  simp only [Matrix.mulVec,dotProduct,crossingTensor,add_mul,Finset.sum_add_distrib,
    ite_and,ite_mul,zero_mul]
  simp only [Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_const_zero,one_mul]
  split_ifs <;> ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PureMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma pureModeTensor_quadratic (q : ℝ) (a : Fin 3) (v : Coord3) :
    v ⬝ᵥ (pureModeTensor q a *ᵥ v) = ∑ i, (if i=a then q else 1)*(v i)^2 := by
  simp only [pureModeTensor,mulVec_diagonal,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma pureModeTensor_bounds {q : ℝ} (hq₁ : 1/8 ≤ q) (hq₂ : q ≤ 10)
    (a : Fin 3) (v : Coord3) :
    (1/8)*(v ⬝ᵥ v) ≤ v ⬝ᵥ (pureModeTensor q a *ᵥ v) ∧
      v ⬝ᵥ (pureModeTensor q a *ᵥ v) ≤ 10*(v ⬝ᵥ v) := by
  rw [pureModeTensor_quadratic]
  simp only [dotProduct,Finset.mul_sum,←sq]
  constructor <;> apply Finset.sum_le_sum <;> intro i _
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    split <;> linarith
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    split <;> linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CascadeTensorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma cubic_axes {a b : Fin 3} (ha : a≠0) (hb : b≠0) (hab : a≠b) :
    a=1 ∧ b=2 ∨ a=2 ∧ b=1 := by
  fin_cases a <;> fin_cases b <;> simp_all

lemma crossingTensor_quadratic {a b : Fin 3} (ha : a≠0) (hb : b≠0) (hab : a≠b)
    (L : ℝ) (x v : Coord3) :
    v ⬝ᵥ (crossingTensor L a b x *ᵥ v) =
      (v 0)^2 + crossingXX L (x 0) (x a) (x b)*(v a)^2+
      2*crossingXY L (x 0) (x a) (x b)*v a*v b+
      crossingYY L (x 0) (x a) (x b)*(v b)^2 := by
  rcases cubic_axes ha hb hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    simp [dotProduct,Fin.sum_univ_three,crossingTensor_mulVec] <;> ring

lemma dotProduct_cubic_axes {a b : Fin 3} (ha : a≠0) (hb : b≠0) (hab : a≠b) (v : Coord3) :
    v ⬝ᵥ v = (v 0)^2+(v a)^2+(v b)^2 := by
  rcases cubic_axes ha hb hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    simp [dotProduct,Fin.sum_univ_three] <;> ring

lemma crossingTensor_bounds {L : ℝ}
    (hL : ∀ z x y X Y : ℝ,
      (1/8)*(X^2+Y^2) ≤ crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ∧
      crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ≤ 10*(X^2+Y^2))
    {a b : Fin 3} (ha : a≠0) (hb : b≠0) (hab : a≠b) (x v : Coord3) :
    (1/8)*(v ⬝ᵥ v) ≤ v ⬝ᵥ (crossingTensor L a b x *ᵥ v) ∧
      v ⬝ᵥ (crossingTensor L a b x *ᵥ v) ≤ 10*(v ⬝ᵥ v) := by
  rw [crossingTensor_quadratic ha hb hab,dotProduct_cubic_axes ha hb hab]
  obtain ⟨hl,hu⟩ := hL (x 0) (x a) (x b) (v a) (v b)
  constructor <;> nlinarith [sq_nonneg (v 0)]

lemma pureModeTensor_normal {a : Fin 3} (ha : a≠0) (q : ℝ) :
    pureModeTensor q a *ᵥ (Pi.single 0 1 : Coord3) = Pi.single 0 1 := by
  ext i
  rw [pureModeTensor,mulVec_diagonal]
  by_cases hi : i=0
  · subst i; simp [Ne.symm ha]
  · simp [Pi.single_eq_of_ne hi]

lemma crossingTensor_normal {a b : Fin 3} (ha : a≠0) (hb : b≠0)
    (L : ℝ) (x : Coord3) :
    crossingTensor L a b x *ᵥ (Pi.single 0 1 : Coord3) = Pi.single 0 1 := by
  ext i
  rw [crossingTensor_mulVec]
  simp [ha,hb,Pi.single_eq_of_ne,Pi.single_apply,eq_comm]

lemma crossingTensor_continuous (L : ℝ) (a b : Fin 3) :
    Continuous (crossingTensor L a b) := by
  have hf := (crossingResidualFirst_smooth L).continuous
  have hg := (crossingResidualSecond_smooth L).continuous
  have hff := (crossingFirst_smooth L).continuous
  have hgg := (crossingSecond_smooth L).continuous
  have hxx : Continuous (fun x : Coord3 => crossingXX L (x 0) (x a) (x b)) := by
    unfold crossingXX crossingHxx
    fun_prop (disch := intro x; positivity)
  have hyy : Continuous (fun x : Coord3 => crossingYY L (x 0) (x a) (x b)) := by
    unfold crossingYY crossingHxx
    fun_prop (disch := intro x; positivity)
  have hxy : Continuous (fun x : Coord3 => crossingXY L (x 0) (x a) (x b)) := by
    unfold crossingXY crossingHxy
    fun_prop (disch := intro x; positivity)
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  unfold crossingTensor
  split_ifs <;> fun_prop

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

attribute [local instance] OAI.ScalarConductivity.cascadeCoefficientMeasurableSpace
local instance cascadeCoefficientBorelSpace : BorelSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

lemma connectorAngular_continuous (K : ℝ) : Continuous (connectorAngular K) := by
  have hf := (connectorProfile_smooth K).continuous
  have hff := (smooth_deriv_infty (smooth_deriv_infty (connectorProfile_smooth K))).continuous
  unfold connectorAngular
  exact hff.div hf (fun x => (connectorProfile_pos K x).ne')

lemma cascadeStageTensor_measurable (L K k : ℝ) (n : ℕ) :
    Measurable (cascadeStageTensor L K k n) := by
  have hp : Continuous (fun x : Coord3 => cascadePhase (cascadeLength L K) k n (x 0)) := by
    unfold cascadePhase
    fun_prop
  have hc : Continuous (fun x : Coord3 =>
      pureModeTensor (connectorAngular K (cascadePhase (cascadeLength L K) k n (x 0))) (cascadeAxis n)) := by
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    simp only [pureModeTensor, Matrix.diagonal_apply]
    split_ifs
    · exact (connectorAngular_continuous K).comp hp
    · exact continuous_const
    · exact continuous_const
  have hx : Continuous (fun x : Coord3 => crossingTensor L (cascadeAxis n) (cascadeAxis (n+1))
      ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)-Pi.single 0 (K+2+L))) :=
    (crossingTensor_continuous L _ _).comp (by fun_prop)
  exact Measurable.ite (isOpen_lt hp continuous_const).measurableSet hc.measurable hx.measurable

lemma cascadeTensor_measurable (L K k : ℝ) : Measurable (cascadeTensor L K k) := by
  have hs : Measurable (fun x : Coord3 => cascadeStageTensor L K k
      (cascadeIndex (cascadeLength L K) k x) x) := by
    apply Measurable.find (cascadeStageTensor_measurable L K k)
    intro n
    have hc : Continuous (fun x : Coord3 => cascadePhase (cascadeLength L K) k n (x 0)) := by
      unfold cascadePhase
      fun_prop
    exact (isClosed_le hc continuous_const).measurableSet.union
      (isClosed_le continuous_const (continuous_const.mul (continuous_apply 0))).measurableSet
  have hp : MeasurableSet {x : Coord3 | 0≤k*x 0 ∧ k*x 0<2*cascadeLength L K} := by
    apply MeasurableSet.inter
    · exact (isClosed_le continuous_const (continuous_const.mul (continuous_apply 0))).measurableSet
    · exact (isOpen_lt (continuous_const.mul (continuous_apply 0)) continuous_const).measurableSet
  exact Measurable.ite hp hs measurable_const

lemma cascadeTensor_normal (L K k : ℝ) (x : Coord3) :
    cascadeTensor L K k x *ᵥ (Pi.single 0 1 : Coord3) = Pi.single 0 1 := by
  unfold cascadeTensor cascadeStageTensor
  split_ifs
  · exact pureModeTensor_normal (cascadeAxis_ne_zero _) _
  · exact crossingTensor_normal (cascadeAxis_ne_zero _) (cascadeAxis_ne_zero _) _ _
  · exact one_mulVec _

lemma cascadeTensor_bounds {L K k : ℝ}
    (hL : ∀ z x y X Y : ℝ,
      (1/8)*(X^2+Y^2) ≤ crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ∧
      crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ≤ 10*(X^2+Y^2))
    (hK : ∀ z, 1/8 ≤ connectorAngular K z ∧ connectorAngular K z≤10)
    (x v : Coord3) :
    (1/8)*(v ⬝ᵥ v) ≤ v ⬝ᵥ (cascadeTensor L K k x *ᵥ v) ∧
      v ⬝ᵥ (cascadeTensor L K k x *ᵥ v) ≤ 10*(v ⬝ᵥ v) := by
  unfold cascadeTensor cascadeStageTensor
  split_ifs
  · exact pureModeTensor_bounds (hK _).1 (hK _).2 _ _
  · exact crossingTensor_bounds hL (cascadeAxis_ne_zero _) (cascadeAxis_ne_zero _)
      (cascadeAxis_ne_succ _) _ _
  · rw [one_mulVec]
    have hp : 0≤v ⬝ᵥ v := by
      apply Finset.sum_nonneg; intro i _; exact mul_self_nonneg _
    constructor <;> nlinarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingEllipticity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma crossing_uniform_ellipticity {M L : ℝ} (hM0 : 1 ≤ M) (hL : 1 ≤ L)
    (hM : ∀ x : ℝ, |deriv smoothTransition x| ≤ M ∧
      |deriv (deriv smoothTransition) x| ≤ M)
    (hsmall : 40*M*exp (-L) ≤ 1/56) (z x y X Y : ℝ) :
    (1/8)*(X^2+Y^2) ≤ crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ∧
    crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ≤ 10*(X^2+Y^2) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hε : 0 ≤ 40*M*exp (-L) := by positivity
  obtain ⟨hr₁,hr₂⟩ := crossing_residual_bounds hM0 hL hM z
  by_cases hz : z ≤ 0
  · obtain ⟨hyy,hxy⟩ := crossing_corrections_left hLp hz x y
    have hratio := (crossing_mode_ratios (L := L) (z := z)).1 hz
    have hα : |crossingResidualSecond L z/(exp (-3*z)*(1:ℝ)^2)| ≤ 40*M*exp (-L) := by
      simpa only [one_pow,mul_one] using hr₂
    obtain ⟨ha,hb⟩ := crossing_coefficients_small (exp_pos _).ne' (by norm_num : (1:ℝ)≠0)
      (by norm_num : (2:ℝ)≠0) hα hratio (by norm_num : |(1:ℝ)/2|≤2) x y
    rw [hyy,hxy]
    exact crossing_quadratic_ellipticity (a := 9) (b := 1/4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε hsmall ha hb X Y
  · have hz' : 0 ≤ z := le_of_not_ge hz
    obtain ⟨hxx,hxy⟩ := crossing_corrections_right hLp hz' x y
    have hratio := (crossing_mode_ratios (L := L) (z := z)).2 hz'
    have heq : crossingResidualFirst L z/(exp (-z)*(2:ℝ)^2) =
        (crossingResidualFirst L z/exp (-z))/4 := by ring
    have hα : |crossingResidualFirst L z/(exp (-z)*(2:ℝ)^2)| ≤ 40*M*exp (-L) := by
      rw [heq,abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)]
      exact (div_le_iff₀ (by norm_num : (0:ℝ)<4)).mpr (by linarith)
    obtain ⟨ha,hb⟩ := crossing_coefficients_small (exp_pos _).ne' (by norm_num : (2:ℝ)≠0)
      (by norm_num : (1:ℝ)≠0) hα hratio (by norm_num : |(2:ℝ)/1|≤2) y x
    have hh := crossing_quadratic_ellipticity (a := 1/4) (b := 9)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε hsmall ha hb Y X
    rw [hxx,hxy]
    dsimp only [crossingYY]
    constructor <;> nlinarith [hh.1,hh.2]

theorem exists_elliptic_crossing : ∃ L : ℝ, 1 ≤ L ∧ ∀ z x y X Y : ℝ,
    (1/8)*(X^2+Y^2) ≤ crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ∧
    crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ≤ 10*(X^2+Y^2) := by
  obtain ⟨M,hM0,hM⟩ := exists_transition_derivative_bound
  obtain ⟨L,hL,hs⟩ := exists_small_crossing_scale hM0
  exact ⟨L,hL,crossing_uniform_ellipticity hM0 hL hM hs⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeWeakEnd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

theorem exists_cascade_parameters : ∃ L K : ℝ, 1≤L ∧ 0<K ∧
    ∀ k : ℝ, ∀ x v : Coord3,
      (1/8)*(v ⬝ᵥ v) ≤ v ⬝ᵥ (cascadeTensor L K k x *ᵥ v) ∧
      v ⬝ᵥ (cascadeTensor L K k x *ᵥ v) ≤ 10*(v ⬝ᵥ v) := by
  obtain ⟨L,hL,hl⟩ := exists_elliptic_crossing
  obtain ⟨M,hM,hm⟩ := exists_transition_derivative_bound
  refine ⟨L,20*M,hL,by linarith,fun k x v => cascadeTensor_bounds hl ?_ x v⟩
  intro z
  have hh := connectorAngular_bounds hM (le_refl (20*M)) (fun x => (hm x).1) z
  exact ⟨hh.1,hh.2.trans (by norm_num)⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_Ending
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Real Set Filter Topology MeasureTheory Matrix

lemma initialConnectorRate_smooth (a b K : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (initialConnectorRate a b K) := by
  exact contDiff_const.add (contDiff_const.mul (smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const K)))

lemma initialConnectorRate_bounds (a b K t : ℝ) :
    min a b ≤ initialConnectorRate a b K t ∧ initialConnectorRate a b K t ≤ max a b := by
  have h0 := smoothTransition.nonneg ((t-1)/K)
  have h1 := smoothTransition.le_one ((t-1)/K)
  have hamin := min_le_left a b
  have hbmin := min_le_right a b
  have hamax := le_max_left a b
  have hbmax := le_max_right a b
  dsimp only [initialConnectorRate]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hamin) (sub_nonneg.mpr h1),
      mul_nonneg (sub_nonneg.mpr hbmin) h0]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hamax) (sub_nonneg.mpr h1),
      mul_nonneg (sub_nonneg.mpr hbmax) h0]

lemma initialConnectorRate_left {a b K t : ℝ} (hK : 0 < K) (ht : t ≤ 1) :
    initialConnectorRate a b K t=a := by
  rw [initialConnectorRate,smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hK.le),mul_zero,add_zero]

lemma initialConnectorRate_right {a b K t : ℝ} (hK : 0 < K) (ht : K+1 ≤ t) :
    initialConnectorRate a b K t=b := by
  rw [initialConnectorRate,smoothTransition.one_of_one_le
    ((le_div_iff₀ hK).mpr (by linarith))]
  ring

lemma initialConnectorRate_deriv (a b K t : ℝ) :
    deriv (initialConnectorRate a b K) t=
      ((b-a)/K)*deriv smoothTransition ((t-1)/K) := by
  have h := ((smoothTransition.contDiff (n:=⊤)).differentiable (by simp) ((t-1)/K)).hasDerivAt
  have hh := ((h.comp t (((hasDerivAt_id t).sub_const 1).div_const K)).const_mul (b-a)).const_add a
  dsimp only [Function.comp_def,id_eq] at hh
  change deriv (fun t => a+(b-a)*smoothTransition ((t-1)/K)) t=_
  rw [hh.deriv]
  ring

lemma exists_initialConnector_length {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℝ,0 < K ∧ ∀ t,|deriv (initialConnectorRate a b K) t| ≤ (min a b)^2/2 := by
  obtain ⟨M,hM,hbound⟩ := exists_transition_derivative_bound
  let m := min a b
  have hm : 0 < m := lt_min ha hb
  let K := (2* |b-a| *M+1)/m^2
  have hMp : 0 < M := by linarith
  have hK : 0 < K := div_pos (by positivity) (sq_pos_of_pos hm)
  have hKe : K*m^2=2* |b-a| *M+1 := div_mul_cancel₀ _ (pow_ne_zero 2 hm.ne')
  refine ⟨K,hK,?_⟩
  intro t
  rw [initialConnectorRate_deriv,abs_mul,abs_div,abs_of_pos hK]
  calc
    _  ≤  (|b-a|/K)*M := mul_le_mul_of_nonneg_left (hbound _).1 (by positivity)
    _  ≤  m^2/2 := by
      rw [div_mul_eq_mul_div,div_le_iff₀ hK]
      nlinarith

lemma initialConnectorProfile_smooth (a b K : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (initialConnectorProfile a b K) := by
  let r : SmoothScalar ℝ := ⟨initialConnectorRate a b K,initialConnectorRate_smooth a b K⟩
  exact ((smoothScalar_contDiff (smoothPrimitive r)).neg).exp

lemma initialConnectorProfile_hasDerivAt (a b K t : ℝ) :
    HasDerivAt (initialConnectorProfile a b K)
      (-initialConnectorRate a b K t*initialConnectorProfile a b K t) t := by
  have hr := (initialConnectorRate_smooth a b K).continuous
  have h := intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable 0 t)
    (hr.stronglyMeasurableAtFilter _ _) hr.continuousAt
  change HasDerivAt (fun t => exp (-(∫ r in (0:ℝ)..t,initialConnectorRate a b K r))) _ t
  exact h.neg.exp.congr_deriv (g':= -initialConnectorRate a b K t*initialConnectorProfile a b K t)
    (by simp only [initialConnectorProfile,Pi.neg_apply]; ring)

lemma initialConnectorAngular_smooth (a b K : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (initialConnectorAngular a b K) :=
  ((initialConnectorRate_smooth a b K).pow 2).sub
    (smooth_deriv_infty (initialConnectorRate_smooth a b K))

lemma initialConnectorAngular_bounds {a b K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : ∀ t,|deriv (initialConnectorRate a b K) t| ≤ (min a b)^2/2) (t : ℝ) :
    (min a b)^2/2 ≤ initialConnectorAngular a b K t ∧
      initialConnectorAngular a b K t ≤ (max a b)^2+(min a b)^2/2 := by
  have hm : 0 < min a b := lt_min ha hb
  have hr := initialConnectorRate_bounds a b K t
  have hd' := abs_le.mp (hd t)
  have hrp : 0 ≤ initialConnectorRate a b K t := hm.le.trans hr.1
  have hs1 := sq_le_sq₀ hm.le hrp |>.mpr hr.1
  have hs2 := sq_le_sq₀ hrp (hrp.trans hr.2) |>.mpr hr.2
  constructor <;> dsimp [initialConnectorAngular] <;> nlinarith

lemma initialConnectorProfile_left {a b K t : ℝ} (hK : 0 < K) (ht : t ≤ 1) :
    initialConnectorProfile a b K t=exp (-a*t) := by
  have hi : (∫ r in (0:ℝ)..t,initialConnectorRate a b K r)=a*t := by
    calc
      _=∫ _r in (0:ℝ)..t,a := intervalIntegral.integral_congr (by
        intro r hr
        apply initialConnectorRate_left hK
        exact (le_max_iff.mp hr.2).elim (by intro h; linarith) (by intro h; linarith))
      _=_ := by simp; ring
  rw [initialConnectorProfile,hi]
  congr 1
  ring

lemma initialConnectorProfile_right {a b K t : ℝ} (hK : 0 < K) (ht : K+1 ≤ t) :
    initialConnectorProfile a b K t=
      initialConnectorProfile a b K (K+2)*exp (-b*(t-(K+2))) := by
  have hi : (∫ r in (K+2)..t,initialConnectorRate a b K r)=b*(t-(K+2)) := by
    calc
      _=∫ _r in (K+2)..t,b := intervalIntegral.integral_congr (by
        intro r hr
        exact initialConnectorRate_right hK ((le_min (by linarith) ht).trans hr.1))
      _=_ := by simp; ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    ((initialConnectorRate_smooth a b K).continuous.intervalIntegrable 0 (K+2))
    ((initialConnectorRate_smooth a b K).continuous.intervalIntegrable (K+2) t)
  rw [hi] at hadd
  unfold initialConnectorProfile
  rw [←hadd,neg_add,exp_add]
  congr 2
  ring

end

section
open Real Set Filter Topology MeasureTheory

lemma cascadeProfile_near_start {L K t : ℝ} (hL : 1 ≤ L) (hK : 0 < K)
    (ht : t∈Icc (-1/4) (1/4)) : cascadeProfile L K t=exp (-t/2) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  rw [cascadeProfile,crossingOn_eq_one hLp (by linarith [ht.1]),
    crossingOff_eq_one hLp (by linarith [ht.2]),one_mul,mul_one,
    connectorProfile_left hK (by linarith [ht.2])]

lemma cascadeProfile_deriv_near_start {L K t : ℝ} (hL : 1 ≤ L) (hK : 0 < K)
    (ht : t∈Ioo (-1/4) (1/4)) : deriv (cascadeProfile L K) t= -(1/2)*exp (-t/2) := by
  have he : cascadeProfile L K =ᶠ[𝓝 t] fun r => exp (-r/2) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact cascadeProfile_near_start hL hK ⟨hr.1.le,hr.2.le⟩
  rw [he.deriv_eq]
  have hd := (((hasDerivAt_id t).neg).div_const 2).exp
  dsimp only [Pi.neg_apply,id_eq] at hd
  rw [hd.deriv]
  ring

lemma cascadePhase_inactive_start {L K k t : ℝ} (hL : 1 ≤ L) (hK : 0 < K)
    (ht : k*t ≤ 1/4) {j : ℕ} (hj : j ≠ 0) :
    cascadePhase (cascadeLength L K) k j t  <  -7*L/2 := by
  have hh := cascadePhase_antitone (D:=cascadeLength L K) (k:=k) (t:=t)
    (show k*t ≤ 2*cascadeLength L K by unfold cascadeLength; linarith)
    (show 1 ≤ j by omega)
  change cascadePhase (cascadeLength L K) k j t  ≤  cascadePhase (cascadeLength L K) k 1 t at hh
  rw [show (1:ℕ)=0+1 from rfl,cascadePhase_succ,cascadePhase_zero] at hh
  unfold cascadeLength at *
  linarith

lemma cascadeValue_near_start {L K k : ℝ} (hL : 1 ≤ L) (hK : 0 < K)
    (A : ℝ) (x : Coord3) (hx : k*x 0∈Icc (-1/4) (1/4)) :
    cascadeValue L K k A x=A*exp (-(k*x 0)/2)*cos (k*x 1) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hz : ∀ j : ℕ,j ≠ 0 → cascadeTerm L K k A j x=0 := by
    intro j hj
    rw [cascadeTerm,cascadeProfile_zero_left hLp
      (cascadePhase_inactive_start hL hK hx.2 hj).le,mul_zero,zero_mul]
  rw [cascadeValue,tsum_eq_single 0 hz,cascadeTerm,cascadePhase_zero,
    cascadeProfile_near_start hL hK hx]
  simp [cascadeAxis]

lemma cascadePotential_near_start {L K k : ℝ} (hL : 1 ≤ L) (hK : 0 < K) (hk : k ≠ 0)
    (A : ℝ) (x : Coord3) (hx : k*x 0∈Ioo (-1/4) (1/4)) (i j : Fin 3) :
    cascadePotential L K k A i j x =
      wedgePotential 0 1 (fun y : Coord3 => -(A/2)*exp (-(k*y 0)/2)*sin (k*y 1)) i j x := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hz : ∀ n : ℕ,n ≠ 0 → (A*cascadeRatio L K^n)*
      cascadePotentialMother L K (cascadeAxis n) (cascadeAxis (n+1)) i j
        ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n))=0 := by
    intro n hn
    let y := (k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)
    have hy : y 0  <  -7*L/2 := by
      dsimp only [y]
      rw [cascade_dilation_time hk]
      exact cascadePhase_inactive_start hL hK hx.2.le hn
    have hb := cascadeBaseStream_zero (K:=K) hLp (cascadeAxis n) y (Or.inl hy)
    have hc := cascadeCrossStream_zero_left (K:=K) hLp (cascadeAxis n) (cascadeAxis (n+1)) y
      (by linarith)
    change (A*cascadeRatio L K^n)*cascadePotentialMother L K (cascadeAxis n) (cascadeAxis (n+1)) i j y=0
    simp [cascadePotentialMother,hb,hc]
  rw [cascadePotential,tsum_eq_single 0 hz]
  have hcenter : cascadeCenter (cascadeLength L K) k 0=0 := by
    ext a
    simp [cascadeCenter]
  simp only [pow_zero,mul_one,hcenter,sub_zero]
  have hc : cascadeCrossStream L K (cascadeAxis 0) (cascadeAxis 1) (k • x)=0 := by
    apply cascadeCrossStream_zero_left hLp
    change k*x 0  <  K+2+L/4
    linarith [hx.2]
  have hb : cascadeBaseStream L K (cascadeAxis 0) (k • x)=
      (-(1/2)*exp (-(k*x 0)/2))*sin (k*x 1) := by
    change deriv (cascadeProfile L K) (k*x 0)*sin (k*x (cascadeAxis 0))=_
    rw [cascadeProfile_deriv_near_start hL hK hx]
    rfl
  unfold cascadePotentialMother
  rw [hc,hb]
  simp only [show cascadeAxis 0=1 from rfl,ite_self,add_zero]
  unfold wedgePotential
  split <;> split <;> ring

end

section
open Set Filter Topology

lemma contDiff_axial_paste {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞}
    {f g : E → F} {t : E → ℝ} {c δ : ℝ}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (ht : Continuous t)
    (hδ : 0 < δ) (he : ∀ x,t x∈Ioo (c-δ) (c+δ) → f x=g x) :
    ContDiff ℝ n (fun x => if t x < c then f x else g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : t x < c
  · apply hf.contDiffAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt ht continuous_const).mem_nhds hx] with y hy
    exact ite_eq_left hy
  · by_cases hx' : c<t x
    · apply hg.contDiffAt.congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const ht).mem_nhds hx'] with y hy
      exact ite_eq_right (not_lt.mpr hy.le)
    · have hxc : t x=c := le_antisymm (le_of_not_gt hx') (le_of_not_gt hx)
      apply hf.contDiffAt.congr_of_eventuallyEq
      filter_upwards [(ht.isOpen_preimage _ isOpen_Ioo).mem_nhds
        (show t x∈Ioo (c-δ) (c+δ) by rw [hxc]; constructor <;> linarith)] with y hy
      split_ifs
      · rfl
      · exact (he y hy).symm

lemma axial_paste_eventually_left {E F : Type*} [TopologicalSpace E]
    {f g : E → F} {t : E → ℝ} {c : ℝ} (ht : Continuous t) {x : E} (hx : t x < c) :
    (fun y => if t y < c then f y else g y)=ᶠ[𝓝 x] f := by
  filter_upwards [(isOpen_lt ht continuous_const).mem_nhds hx] with y hy
  exact ite_eq_left hy

end

section
open Real Set Filter Topology MeasureTheory Matrix

lemma finiteEnding_value_overlap {a J L K : ℝ} (hJ : 0 < J) (hL : 1 ≤ L) (hK : 0 < K)
    (x : Coord3) (hx : x 0∈Ioo ((J+2)-1/4) ((J+2)+1/4)) :
    pureModeValue (initialConnectorProfile a (1/2) J) 1 x=
      cascadeValue L K 1 (initialConnectorProfile a (1/2) J (J+2))
        (x-Pi.single 0 (J+2)) := by
  have hs : 1*((x-Pi.single 0 (J+2) : Coord3) 0)∈Icc (-1/4) (1/4) := by
    simp only [one_mul,Pi.sub_apply,Pi.single_eq_same]
    constructor <;> linarith [hx.1,hx.2]
  rw [cascadeValue_near_start hL hK _ _ hs,pureModeValue,
    initialConnectorProfile_right hJ (show J+1 ≤ x 0 by linarith [hx.1])]
  simp only [one_mul,Pi.sub_apply,Pi.single_eq_same,
    Pi.single_eq_of_ne (show (1:Fin 3)≠0 by decide),sub_zero]
  congr 2
  ring_nf

lemma finiteEnding_potential_overlap {a J L K : ℝ} (hJ : 0 < J) (hL : 1 ≤ L) (hK : 0 < K)
    (x : Coord3) (hx : x 0∈Ioo ((J+2)-1/4) ((J+2)+1/4)) (i j : Fin 3) :
    pureModePotential (initialConnectorProfile a (1/2) J) 1 i j x=
      cascadePotential L K 1 (initialConnectorProfile a (1/2) J (J+2)) i j
        (x-Pi.single 0 (J+2)) := by
  have hs : 1*((x-Pi.single 0 (J+2) : Coord3) 0)∈Ioo (-1/4) (1/4) := by
    simp only [one_mul,Pi.sub_apply,Pi.single_eq_same]
    constructor <;> linarith [hx.1,hx.2]
  rw [cascadePotential_near_start hL hK (by norm_num) _ _ hs,pureModePotential,
    wedgePotential_as_mul,wedgePotential_as_mul]
  simp only [one_mul,Pi.sub_apply,Pi.single_eq_same,
    Pi.single_eq_of_ne (show (1:Fin 3)≠0 by decide),sub_zero]
  rw [(initialConnectorProfile_hasDerivAt a (1/2) J (x 0)).deriv,
    initialConnectorRate_right hJ (show J+1 ≤ x 0 by linarith [hx.1]),
    initialConnectorProfile_right hJ (show J+1 ≤ x 0 by linarith [hx.1])]
  congr 1
  ring_nf

lemma finiteEndingValue_C2 {a J L K : ℝ} (hJ : 0 < J) (hL : 1 ≤ L) (hK : 0 < K) :
    ContDiff ℝ 2 (finiteEndingValue a J L K) := by
  apply contDiff_axial_paste (δ:=1/4) ?_ ?_ (continuous_apply 0) (by norm_num)
    (finiteEnding_value_overlap hJ hL hK)
  · have h := (initialConnectorProfile_smooth a (1/2) J).of_le (show (2:WithTop ℕ∞) ≤ ↑(⊤:ℕ∞) by norm_cast)
    unfold pureModeValue
    exact (h.comp (contDiff_apply ℝ ℝ 0)).mul ((contDiff_apply ℝ ℝ 1).cos)
  · exact (cascadeValue_C2 hL hK (by norm_num : (1:ℝ)≠0) _).comp
      (contDiff_id.sub contDiff_const)

lemma finiteEndingPotential_C2 {a J L K : ℝ} (hJ : 0 < J) (hL : 1 ≤ L) (hK : 0 < K)
    (i j : Fin 3) : ContDiff ℝ 2 (finiteEndingPotential a J L K i j) := by
  apply contDiff_axial_paste (δ:=1/4) ?_ ?_ (continuous_apply 0) (by norm_num)
    (fun x hx => finiteEnding_potential_overlap hJ hL hK x hx i j)
  · have h := (smooth_deriv_infty (initialConnectorProfile_smooth a (1/2) J)).of_le
      (show (2:WithTop ℕ∞) ≤ ↑(⊤:ℕ∞) by norm_cast)
    have hs : ContDiff ℝ 2 (fun x : Coord3 => deriv (initialConnectorProfile a (1/2) J) (x 0)*sin (x 1)) :=
      (h.comp (contDiff_apply ℝ ℝ 0)).mul ((contDiff_apply ℝ ℝ 1).sin)
    unfold pureModePotential wedgePotential
    split <;> split
    · exact hs.sub hs
    · exact hs.sub contDiff_const
    · exact contDiff_const.sub hs
    · exact contDiff_const.sub contDiff_const
  · exact (cascadePotential_C2 hL hK 1 _ i j).comp (contDiff_id.sub contDiff_const)

lemma finiteEndingValue_initial {a J L K : ℝ} (hJ : 0 < J) (x : Coord3) (hx : x 0 ≤ 1) :
    finiteEndingValue a J L K x=exp (-a*x 0)*cos (x 1) := by
  rw [finiteEndingValue,ite_eq_left (show x 0<J+2 by linarith),pureModeValue,
    initialConnectorProfile_left hJ hx]

lemma finiteEndingValue_terminal {a J L K : ℝ} (_ : 0 < J) (hL : 1 ≤ L) (hK : 0 < K)
    (x : Coord3) (hx : J+2+2*cascadeLength L K ≤ x 0) : finiteEndingValue a J L K x=0 := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hD := cascade_length_positive hLp hK
  rw [finiteEndingValue,ite_eq_right (show ¬x 0<J+2 by linarith)]
  apply cascadeValue_terminal hLp hK
  simp only [one_mul,Pi.sub_apply,Pi.single_eq_same]
  linarith

attribute [local instance] OAI.ScalarConductivity.endingMatrixMeasurableSpace
local instance endingMatrixBorelSpace : BorelSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

lemma finiteEndingTensor_measurable (a J L K : ℝ) : Measurable (finiteEndingTensor a J L K) := by
  apply Measurable.ite ((isOpen_lt (continuous_apply 0) continuous_const).measurableSet)
  · have h : Continuous (fun x : Coord3 => pureModeTensor (initialConnectorAngular a (1/2) J (x 0)) 1) := by
      apply continuous_matrix
      intro i j
      unfold pureModeTensor Matrix.diagonal
      simp only [Matrix.of_apply]
      split_ifs
      · exact (initialConnectorAngular_smooth a (1/2) J).continuous.comp (continuous_apply 0)
      all_goals exact continuous_const
    exact h.measurable
  · exact (cascadeTensor_measurable L K 1).comp (by fun_prop)

lemma finiteEndingTensor_normal (a J L K : ℝ) (x : Coord3) :
    finiteEndingTensor a J L K x*ᵥPi.single 0 1=Pi.single 0 1 := by
  unfold finiteEndingTensor
  split_ifs
  · exact pureModeTensor_normal (by decide : (1:Fin 3)≠0) _
  · exact cascadeTensor_normal _ _ _ _

end

open Real Set Filter Topology MeasureTheory Matrix

lemma pureModeTensor_general_bounds {q c C : ℝ} (hc : c≤1) (hC : 1≤C)
    (hcq : c≤q) (hqC : q≤C) (i : Fin 3) (v : Coord3) :
    c*(v ⬝ᵥ v)≤v ⬝ᵥ (pureModeTensor q i*ᵥv) ∧
      v ⬝ᵥ (pureModeTensor q i*ᵥv)≤C*(v ⬝ᵥ v) := by
  rw [pureModeTensor_quadratic]
  simp only [dotProduct,Finset.mul_sum,←sq]
  constructor <;> apply Finset.sum_le_sum <;> intro j _
  · exact mul_le_mul_of_nonneg_right (by split <;> assumption) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right (by split <;> assumption) (sq_nonneg _)

theorem exists_finiteEnding_parameters {a : ℝ} (ha : 0<a) :
    ∃ J L K c C : ℝ,0<J ∧ 1≤L ∧ 0<K ∧ 0 < c ∧ c≤C ∧
      ∀ x v : Coord3,c*(v ⬝ᵥ v)≤v ⬝ᵥ (finiteEndingTensor a J L K x*ᵥv) ∧
        v ⬝ᵥ (finiteEndingTensor a J L K x*ᵥv)≤C*(v ⬝ᵥ v) := by
  obtain ⟨J,hJ,hd⟩ := exists_initialConnector_length ha (by norm_num : (0:ℝ)<1/2)
  obtain ⟨L,K,hL,hK,hLK⟩ := exists_cascade_parameters
  let c := min (1/8) ((min a (1/2))^2/2)
  let C := max 10 ((max a (1/2))^2+(min a (1/2))^2/2)
  have hmin : 0 < min a (1/2) := lt_min ha (by norm_num)
  have hc : 0 < c := lt_min (by norm_num) (div_pos (sq_pos_of_pos hmin) (by norm_num))
  have hc8 : c≤1/8 := min_le_left _ _
  have hcq : c≤(min a (1/2))^2/2 := min_le_right _ _
  have hC10 : 10≤C := le_max_left _ _
  have hCq : (max a (1/2))^2+(min a (1/2))^2/2≤C := le_max_right _ _
  refine ⟨J,L,K,c,C,hJ,hL,hK,hc,by linarith,?_⟩
  intro x v
  unfold finiteEndingTensor
  split_ifs
  · have hq := initialConnectorAngular_bounds ha (by norm_num : (0:ℝ)<1/2) hd (x 0)
    exact pureModeTensor_general_bounds (by linarith) (by linarith) (hcq.trans hq.1) (hq.2.trans hCq) _ _
  · have hb := hLK 1 (x-Pi.single 0 (J+2)) v
    have hv : 0≤v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    exact ⟨(mul_le_mul_of_nonneg_right hc8 hv).trans hb.1,
      hb.2.trans (mul_le_mul_of_nonneg_right hC10 hv)⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_EndingCoordinateTransport
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma permutedDilation_smooth (e : Equiv.Perm (Fin 3)) (r : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (permutedDilation e r) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.mul (contDiff_apply ℝ ℝ (e i))

lemma permutedTensor_quadratic (e : Equiv.Perm (Fin 3)) (A : Mat3) (v : Coord3) :
    v ⬝ᵥ ((fun i j => A (e.symm i) (e.symm j))*ᵥv) =
      (fun i => v (e i)) ⬝ᵥ (A*ᵥ(fun i => v (e i))) := by
  simp only [Matrix.mulVec,dotProduct]
  have hi := Equiv.sum_comp e (fun i => v i*∑ j,A (e.symm i) (e.symm j)*v j)
  rw [←hi]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Equiv.symm_apply_apply]
  congr 1
  have hj := Equiv.sum_comp e (fun j => A i (e.symm j)*v j)
  simpa only [Equiv.symm_apply_apply] using hj.symm

end ScalarConductivity



namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma angularAxisSwap_apply (i : Fin 3) : angularAxisSwap i=![0,2,1] i := by
  fin_cases i <;> decide

lemma alignedEndingValue_C2 {lam k J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ContDiff ℝ 2 (alignedEndingValue lam k J L K) :=
  (finiteEndingValue_C2 hJ hL hK).comp ((permutedDilation_smooth angularAxisSwap k).of_le (show (2:WithTop ℕ∞) ≤ ↑(⊤:ℕ∞) by norm_cast))

lemma alignedEndingPotential_C2 {lam k J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (i j : Fin 3) :
    ContDiff ℝ 2 (alignedEndingPotential lam k J L K i j) :=
  (finiteEndingPotential_C2 hJ hL hK _ _).comp ((permutedDilation_smooth angularAxisSwap k).of_le (show (2:WithTop ℕ∞) ≤ ↑(⊤:ℕ∞) by norm_cast))

attribute [local instance] OAI.ScalarConductivity.endingCoordinateTransportMeasurableSpace
local instance endingCoordinateTransportBorelSpace_rceb1e7_1 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))
lemma alignedEndingTensor_measurable (lam k J L K : ℝ) : Measurable (alignedEndingTensor lam k J L K) := by
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro j
  exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
    ((finiteEndingTensor_measurable _ _ _ _).comp (permutedDilation_smooth _ _).continuous.measurable))

lemma alignedEndingTensor_normal (lam k J L K : ℝ) (x : Coord3) :
    alignedEndingTensor lam k J L K x*ᵥPi.single 0 1=Pi.single 0 1 := by
  ext i
  have hh := congrFun (finiteEndingTensor_normal (lam/k) J L K (permutedDilation angularAxisSwap k x)) (angularAxisSwap i)
  fin_cases i <;> simpa [alignedEndingTensor, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    angularAxisSwap_apply, Pi.single_apply] using hh

lemma alignedEnding_initial {lam k J L K : ℝ} (hk : 0<k) (hJ : 0<J) (x : Coord3) (ht : k*x 0≤1) :
    alignedEndingValue lam k J L K x=exp (-lam*x 0)*cos (k*x 2) := by
  have h0 : permutedDilation angularAxisSwap k x 0=k*x 0 := by simp [permutedDilation,angularAxisSwap_apply]
  have h1 : permutedDilation angularAxisSwap k x 1=k*x 2 := by simp [permutedDilation,angularAxisSwap_apply]
  rw [alignedEndingValue,finiteEndingValue_initial hJ _ (by simpa only [h0] using ht),h0,h1]
  congr 2
  field_simp

lemma alignedEnding_terminal {lam k J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
    (x : Coord3) (ht : J+2+2*cascadeLength L K≤k*x 0) :
    alignedEndingValue lam k J L K x=0 := by
  apply finiteEndingValue_terminal hJ hL hK
  simpa only [permutedDilation,angularAxisSwap_apply,Matrix.cons_val_zero] using ht

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusNonresonance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set

lemma torusQuadratic_sublevel_finite {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) : {h : Fin 2 → ℤ | torusQuadratic s h ≤ R}.Finite := by
  obtain ⟨N,hN⟩ := exists_nat_gt (|2*R|+1)
  have hN0 : 0 < (N:ℝ) := lt_trans (by positivity) hN
  apply (Set.Finite.pi' (fun _ : Fin 2 => Set.finite_Icc (-(N:ℤ)) N)).subset
  intro h hh i
  change torusQuadratic s h ≤ R at hh
  have hq := hs (h 0) (h 1)
  change (1/2)*((h 0:ℝ)^2+(h 1:ℝ)^2) ≤ torusQuadratic s h at hq
  have hb : (h i:ℝ)^2 ≤ 2*R := by
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at *
    · nlinarith [sq_nonneg (h 1:ℝ)]
    · nlinarith [sq_nonneg (h 0:ℝ)]
  have hN2 : 2*R < (N:ℝ)^2 := by
    have habs := le_abs_self (2*R)
    nlinarith [sq_nonneg ((N:ℝ)-1)]
  have hbound : -(N:ℝ) ≤ (h i:ℝ) ∧ (h i:ℝ) ≤ N := by
    constructor
    · nlinarith [sq_nonneg ((h i:ℝ)+(N:ℝ))]
    · nlinarith [sq_nonneg ((h i:ℝ)-(N:ℝ))]
  exact_mod_cast hbound

lemma torusQuadratic_pos {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {h : Fin 2 → ℤ} (hh : h≠0) : 0<torusQuadratic s h := by
  have hs' := hs (h 0) (h 1)
  change (1/2)*((h 0:ℝ)^2+(h 1:ℝ)^2) ≤ torusQuadratic s h at hs'
  have hn : (h 0:ℝ)≠0 ∨ (h 1:ℝ)≠0 := by
    by_contra! hc
    apply hh
    have h0 : h 0=0 := by exact_mod_cast hc.1
    have h1 : h 1=0 := by exact_mod_cast hc.2
    ext i; fin_cases i <;> simp [h0,h1]
  rcases hn with hn|hn
  · nlinarith [sq_pos_of_ne_zero hn,sq_nonneg (h 1:ℝ)]
  · nlinarith [sq_pos_of_ne_zero hn,sq_nonneg (h 0:ℝ)]

lemma torus_modes_have_first {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {M : Set (Fin 2 → ℤ)} (hne : M.Nonempty) :
    ∃ h∈M, ∀ l∈M, torusQuadratic s h ≤ torusQuadratic s l := by
  obtain ⟨h₀,hh₀⟩ := hne
  let K := M∩{h | torusQuadratic s h ≤ torusQuadratic s h₀}
  have hK : K.Finite := (torusQuadratic_sublevel_finite hs _).subset inter_subset_right
  obtain ⟨h,hh,hmin⟩ := Set.exists_min_image K (torusQuadratic s) hK ⟨h₀,hh₀,show torusQuadratic s h₀ ≤ torusQuadratic s h₀ from le_rfl⟩
  refine ⟨h,hh.1,fun l hl => ?_⟩
  by_cases hll : torusQuadratic s l ≤ torusQuadratic s h₀
  · exact hmin l ⟨hl,hll⟩
  · exact hh.2.trans (le_of_not_ge hll)

theorem torus_leading_pair_gap {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hres : ∀ h l : Fin 2 → ℤ, torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h)
    {M : Set (Fin 2 → ℤ)} (hne : M.Nonempty) (hzero : 0∉M) :
    ∃ h∈M, 0<torusQuadratic s h ∧ ∃ δ : ℝ, 0<δ ∧
      ∀ l∈M, l≠h → l≠-h → torusQuadratic s h+δ ≤ torusQuadratic s l := by
  obtain ⟨h,hh,hmin⟩ := torus_modes_have_first hs hne
  refine ⟨h,hh,torusQuadratic_pos hs (fun he => hzero (he ▸ hh)),?_⟩
  let N := {l∈M | l≠h ∧ l≠-h}
  by_cases hN : N.Nonempty
  · obtain ⟨g,hg,hgmin⟩ := torus_modes_have_first hs hN
    have hlt : torusQuadratic s h<torusQuadratic s g := by
      apply lt_of_le_of_ne (hmin g hg.1)
      intro he
      exact (hres h g he).elim hg.2.1 hg.2.2
    refine ⟨torusQuadratic s g-torusQuadratic s h,sub_pos.mpr hlt,?_⟩
    intro l hl hle hln
    have hi := hgmin l ⟨hl,hle,hln⟩
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro l hl hle hln
    exact False.elim (hN ⟨l,hl,hle,hln⟩)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusFlatMode
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology

lemma flatPhaseMode_translation (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (phase T : ℝ)
    (x : Fin 3 → ℝ) :
    flatPhaseMode s h phase (x+![T,0,0]) = exp (-torusRate s h*T)*flatPhaseMode s h phase x := by
  simp only [flatPhaseMode,torusAngular,add_apply,
    smul_apply,ContinuousLinearMap.proj_apply,Pi.add_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    smul_eq_mul,add_zero]
  rw [mul_add,exp_add]
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CascadePeriodicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma angularShift_apply (T : ℝ) (n : Fin 2 → ℤ) (i : Fin 3) :
    angularShift T n i=T*(angularInteger n i:ℝ) := by
  fin_cases i <;> simp [angularShift,angularInteger]

lemma sin_int_angular_shift (q : ℤ) (n : Fin 2 → ℤ) (x : Coord3) (i : Fin 3) :
    sin ((q:ℝ)*(x+angularShift (2*Real.pi) n) i)=sin ((q:ℝ)*x i) := by
  have he : (q:ℝ)*(x+angularShift (2*Real.pi) n) i=
      (q:ℝ)*x i+((q*angularInteger n i:ℤ):ℝ)*(2*Real.pi) := by
    simp only [Pi.add_apply,angularShift_apply,Int.cast_mul]
    ring
  rw [he,sin_add_int_mul_two_pi]

lemma cos_int_angular_shift (q : ℤ) (n : Fin 2 → ℤ) (x : Coord3) (i : Fin 3) :
    cos ((q:ℝ)*(x+angularShift (2*Real.pi) n) i)=cos ((q:ℝ)*x i) := by
  have he : (q:ℝ)*(x+angularShift (2*Real.pi) n) i=
      (q:ℝ)*x i+((q*angularInteger n i:ℤ):ℝ)*(2*Real.pi) := by
    simp only [Pi.add_apply,angularShift_apply,Int.cast_mul]
    ring
  rw [he,cos_add_int_mul_two_pi]

lemma cascadeTerm_angularPeriodic (L K A : ℝ) (k : ℤ) (j : ℕ) :
    AngularPeriodic (2*Real.pi) (cascadeTerm L K k A j) := by
  intro n x
  have hc := cos_int_angular_shift (k*2^j) n x (cascadeAxis j)
  push_cast at hc
  simpa only [cascadeTerm,Pi.add_apply,angularShift,Matrix.cons_val_zero,add_zero] using
    congrArg (fun z => (A*cascadeRatio L K^j)*
      cascadeProfile L K (cascadePhase (cascadeLength L K) k j (x 0))*z) hc

lemma cascadeValue_angularPeriodic (L K A : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (cascadeValue L K k A) := by
  intro n x
  apply tsum_congr
  intro j
  exact cascadeTerm_angularPeriodic L K A k j n x

lemma crossingTensor_angularPeriodic (L : ℝ) (a b : Fin 3) :
    AngularPeriodic (2*Real.pi) (crossingTensor L a b) := by
  intro n x
  have hs (i : Fin 3) : sin ((x+angularShift (2*Real.pi) n) i)=sin (x i) := by
    simpa using sin_int_angular_shift 1 n x i
  have hc (i : Fin 3) : cos ((x+angularShift (2*Real.pi) n) i)=cos (x i) := by
    simpa using cos_int_angular_shift 1 n x i
  have hs2 (i : Fin 3) : sin (2*(x+angularShift (2*Real.pi) n) i)=sin (2*x i) := by
    simpa using sin_int_angular_shift 2 n x i
  have hc2 (i : Fin 3) : cos (2*(x+angularShift (2*Real.pi) n) i)=cos (2*x i) := by
    simpa using cos_int_angular_shift 2 n x i
  have hzero : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  ext i j
  simp only [crossingTensor,crossingXX,crossingYY,crossingXY,crossingHxx,crossingHxy,
    one_mul,hs,hc,hs2,hc2,hzero]

lemma angularShift_dilation (q : ℤ) (n : Fin 2 → ℤ) (x c d : Coord3) :
    (q:ℝ) • (x+angularShift (2*Real.pi) n-c)-d=
      ((q:ℝ) • (x-c)-d)+angularShift (2*Real.pi) (fun i => q*n i) := by
  have hshift : (q:ℝ) • angularShift (2*Real.pi) n=
      angularShift (2*Real.pi) (fun i => q*n i) := by
    ext i
    fin_cases i
    · change (q:ℝ)*0=0
      ring
    · change (q:ℝ)*((2*Real.pi)*(n 0:ℝ))=(2*Real.pi)*((q*n 0:ℤ):ℝ)
      push_cast
      ring
    · change (q:ℝ)*((2*Real.pi)*(n 1:ℝ))=(2*Real.pi)*((q*n 1:ℤ):ℝ)
      push_cast
      ring
  rw [smul_sub,smul_add,smul_sub,hshift]
  abel

lemma cascadeStageTensor_angularPeriodic (L K : ℝ) (k : ℤ) (j : ℕ) :
    AngularPeriodic (2*Real.pi) (cascadeStageTensor L K k j) := by
  intro n x
  have hs : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  unfold cascadeStageTensor
  rw [hs]
  split_ifs
  · rfl
  · have he := angularShift_dilation (k*2^j) n x (cascadeCenter (cascadeLength L K) k j)
        (Pi.single 0 (K+2+L))
    push_cast at he
    rw [he,crossingTensor_angularPeriodic]

lemma cascadeTensor_angularPeriodic (L K : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (cascadeTensor L K k) := by
  intro n x
  have hs : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  have hi : cascadeIndex (cascadeLength L K) k (x+angularShift (2*Real.pi) n)=
      cascadeIndex (cascadeLength L K) k x := by simp only [cascadeIndex,hs]
  unfold cascadeTensor
  rw [hs,hi]
  split_ifs
  · exact cascadeStageTensor_angularPeriodic L K k _ n x
  · rfl

lemma cascadeValue_one_angularPeriodic (L K A : ℝ) :
    AngularPeriodic (2*Real.pi) (cascadeValue L K 1 A) := by
  simpa only [Int.cast_one] using (cascadeValue_angularPeriodic L K A (1:ℤ))

lemma cascadeTensor_one_angularPeriodic (L K : ℝ) :
    AngularPeriodic (2*Real.pi) (cascadeTensor L K 1) := by
  simpa only [Int.cast_one] using (cascadeTensor_angularPeriodic L K (1:ℤ))

lemma finiteEndingValue_angularPeriodic (a J L K : ℝ) :
    AngularPeriodic (2*Real.pi) (finiteEndingValue a J L K) := by
  intro n x
  have hs : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  have he : x+angularShift (2*Real.pi) n-Pi.single 0 (J+2)=
      (x-Pi.single 0 (J+2))+angularShift (2*Real.pi) n := by abel
  unfold finiteEndingValue
  rw [hs]
  split_ifs
  · unfold pureModeValue
    rw [hs]
    have hh := cos_int_angular_shift 1 n x 1
    simpa using congrArg (fun z => initialConnectorProfile a (1/2) J (x 0)*z) hh
  · rw [he]
    apply cascadeValue_one_angularPeriodic

lemma finiteEndingTensor_angularPeriodic (a J L K : ℝ) :
    AngularPeriodic (2*Real.pi) (finiteEndingTensor a J L K) := by
  intro n x
  have hs : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  have he : x+angularShift (2*Real.pi) n-Pi.single 0 (J+2)=
      (x-Pi.single 0 (J+2))+angularShift (2*Real.pi) n := by abel
  unfold finiteEndingTensor
  rw [hs]
  split_ifs
  · rfl
  · rw [he]
    exact cascadeTensor_one_angularPeriodic L K n (x-Pi.single 0 (J+2))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AlignedEndingData
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma alignedEndingTensor_bounds {lam k J L K c C : ℝ}
    (hb : ∀ x v : Coord3,c*(v ⬝ᵥ v)≤v ⬝ᵥ (finiteEndingTensor (lam/k) J L K x*ᵥv) ∧
      v ⬝ᵥ (finiteEndingTensor (lam/k) J L K x*ᵥv)≤C*(v ⬝ᵥ v))
    (x v : Coord3) :
    c*(v ⬝ᵥ v)≤v ⬝ᵥ (alignedEndingTensor lam k J L K x*ᵥv) ∧
      v ⬝ᵥ (alignedEndingTensor lam k J L K x*ᵥv)≤C*(v ⬝ᵥ v) := by
  have h := hb (permutedDilation angularAxisSwap k x) (fun i => v (angularAxisSwap i))
  have hn : (fun i => v (angularAxisSwap i)) ⬝ᵥ (fun i => v (angularAxisSwap i))=v ⬝ᵥ v :=
    Equiv.sum_comp angularAxisSwap (fun i => v i*v i)
  rw [hn] at h
  have hq := permutedTensor_quadratic angularAxisSwap
    (finiteEndingTensor (lam/k) J L K (permutedDilation angularAxisSwap k x)) v
  change v ⬝ᵥ (alignedEndingTensor lam k J L K x*ᵥv)=_ at hq
  simpa only [hq] using h

lemma permutedDilation_angularShift (k : ℤ) (n : Fin 2 → ℤ) (x : Coord3) :
    permutedDilation angularAxisSwap (k:ℝ) (x+angularShift (2*Real.pi) n)=
      permutedDilation angularAxisSwap (k:ℝ) x+
        angularShift (2*Real.pi) ![k*n 1,k*n 0] := by
  ext i
  fin_cases i <;> simp [permutedDilation,angularAxisSwap_apply,angularShift] <;> ring

lemma alignedEndingValue_angularPeriodic (lam J L K : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (alignedEndingValue lam k J L K) := by
  intro n x
  dsimp only [alignedEndingValue]
  rw [permutedDilation_angularShift]
  exact finiteEndingValue_angularPeriodic _ _ _ _ _ _

lemma alignedEndingTensor_angularPeriodic (lam J L K : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (alignedEndingTensor lam k J L K) := by
  intro n x
  ext i j
  dsimp only [alignedEndingTensor]
  rw [permutedDilation_angularShift,finiteEndingTensor_angularPeriodic]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AlignedEndingRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma delayedEndingValue_C2 {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ContDiff ℝ 2 (delayedEndingValue lam k J L K R) :=
  contDiff_const.mul ((alignedEndingValue_C2 hJ hL hK).comp (contDiff_id.sub contDiff_const))

lemma delayedEndingValue_initial_of_bound {lam k J L K R : ℝ} (hk : 0<k) (hJ : 0<J)
    (x : Coord3) (hx : k*(x 0-R)≤1) :
    delayedEndingValue lam k J L K R x=exp (-lam*x 0)*cos (k*x 2) := by
  rw [delayedEndingValue,alignedEnding_initial hk hJ _ (by simpa using hx)]
  simp only [Pi.sub_apply,Pi.single_eq_same,Pi.single_eq_of_ne (show (2:Fin 3)≠0 by decide),sub_zero]
  rw [←mul_assoc,←exp_add]
  congr 2
  ring

lemma delayedEndingValue_initial {lam k J L K R : ℝ} (hk : 0<k) (hJ : 0<J)
    (x : Coord3) (hx : x 0≤R) :
    delayedEndingValue lam k J L K R x=exp (-lam*x 0)*cos (k*x 2) := by
  apply delayedEndingValue_initial_of_bound hk hJ
  have hh := mul_nonpos_of_nonneg_of_nonpos hk.le (sub_nonpos.mpr hx)
  linarith

lemma delayedEndingValue_terminal {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
    (x : Coord3) (hx : J+2+2*cascadeLength L K≤k*(x 0-R)) :
    delayedEndingValue lam k J L K R x=0 := by
  rw [delayedEndingValue,alignedEnding_terminal hJ hL hK _ (by simpa using hx),mul_zero]

lemma delayedEndingValue_periodic (lam J L K R : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (delayedEndingValue lam k J L K R) := by
  intro n x
  change exp (-lam*R)*alignedEndingValue lam k J L K (x+angularShift (2*Real.pi) n-Pi.single 0 R)=_
  rw [add_sub_right_comm,alignedEndingValue_angularPeriodic]
  rfl

lemma matchedEndingPair_C2 {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ 2 u)
    {lam k J L K : ℝ} (hk : 0<k) (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
    (he : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)]) :
    ContDiff ℝ 2 (matchedEndingPair u lam k J L K) := by
  have hv : ContDiff ℝ 2 (fun x : Coord3 => ![x 0,delayedEndingValue lam k J L K 7 x]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_apply ℝ ℝ 0
    · exact delayedEndingValue_C2 hJ hL hK
  apply contDiff_axial_paste hu hv (continuous_apply 0) (δ:=1/4) (by norm_num)
  intro x hx
  rw [he x (by linarith [hx.1]),delayedEndingValue_initial hk hJ x (by linarith [hx.2])]

lemma matchedEndingPair_periodic {u : Coord3 → Fin 2 → ℝ}
    (hu : AngularPeriodic (2*Real.pi) u) (lam J L K : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (matchedEndingPair u lam k J L K) := by
  intro n x
  have ht : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  simp only [matchedEndingPair,ht,hu n x,delayedEndingValue_periodic _ _ _ _ _ _ n x]

lemma matchedEndingPair_terminal {u : Coord3 → Fin 2 → ℝ} {lam k J L K : ℝ}
    (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (x : Coord3)
    (hx : 13/2≤x 0) (hterm : J+2+2*cascadeLength L K≤k*(x 0-7)) :
    matchedEndingPair u lam k J L K x=![x 0,0] := by
  rw [matchedEndingPair,ite_eq_right (not_lt.mpr hx),delayedEndingValue_terminal hJ hL hK _ hterm]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AxialFluxBlend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma axialFluxBlend_C1 {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) {F G : Coord3 → Coord3}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) : ContDiff ℝ 1 (axialFluxBlend χ F G) := by
  apply contDiff_pi.mpr
  intro i
  exact ((contDiff_const.sub (hχ.comp (contDiff_apply ℝ ℝ 0))).mul (contDiff_pi.mp hF i)).add
    ((hχ.comp (contDiff_apply ℝ ℝ 0)).mul (contDiff_pi.mp hG i))

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma delayedEndingPotential_C2 {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (i j : Fin 3) :
    ContDiff ℝ 2 (delayedEndingPotential lam k J L K R i j) :=
  contDiff_const.mul ((alignedEndingPotential_C2 hJ hL hK i j).comp (contDiff_id.sub contDiff_const))

lemma delayedEndingFlux_C1 {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ContDiff ℝ 1 (potentialCurl (delayedEndingPotential lam k J L K R)) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.sum
  intro j _
  exact direction_C1 (delayedEndingPotential_C2 hJ hL hK i j) _

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_EndingJoinCutoff
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma endingJoinCutoff_smooth : ContDiff ℝ (↑(⊤:ℕ∞)) endingJoinCutoff :=
  smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma endingJoinCutoff_bounds (t : ℝ) : 0≤endingJoinCutoff t ∧ endingJoinCutoff t≤1 :=
  ⟨smoothTransition.nonneg _,smoothTransition.le_one _⟩

lemma endingJoinCutoff_left {t : ℝ} (ht : t≤6) : endingJoinCutoff t=0 :=
  smoothTransition.zero_of_nonpos (by linarith)

lemma endingJoinCutoff_right {t : ℝ} (ht : 7≤t) : endingJoinCutoff t=1 :=
  smoothTransition.one_of_one_le (by linarith)

lemma endingJoinTensor_left (D : Coord3 → Mat3) (lam k J L K : ℝ) (x : Coord3) (hx : x 0≤6) :
    endingJoinTensor D lam k J L K x=D x := by
  simp [endingJoinTensor,endingJoinCutoff_left hx]

lemma endingJoinTensor_right (D : Coord3 → Mat3) (lam k J L K : ℝ) (x : Coord3) (hx : 7≤x 0) :
    endingJoinTensor D lam k J L K x=delayedEndingTensor lam k J L K 7 x := by
  simp [endingJoinTensor,endingJoinCutoff_right hx]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_EndingJoinElliptic
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

attribute [local instance] OAI.ScalarConductivity.endingJoinEllipticMeasurableSpace
local instance endingJoinEllipticBorelSpace_rceb1e7_1 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))
lemma delayedEndingTensor_measurable (lam k J L K R : ℝ) :
    Measurable (delayedEndingTensor lam k J L K R) :=
  (alignedEndingTensor_measurable _ _ _ _ _).comp (measurable_id.sub measurable_const)

lemma endingJoinTensor_measurable {D : Coord3 → Mat3} (hD : Measurable D) (lam k J L K : ℝ) :
    Measurable (endingJoinTensor D lam k J L K) := by
  have hh : Measurable (fun x : Coord3 => endingJoinCutoff (x 0)) := endingJoinCutoff_smooth.continuous.measurable.comp (measurable_pi_apply (0:Fin 3))
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro j
  exact ((measurable_const.sub hh).mul ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hD))).add
    (hh.mul ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (delayedEndingTensor_measurable _ _ _ _ _ _))))

lemma convexTensor_quadratic (A B : Mat3) (t : ℝ) (v : Coord3) :
    v ⬝ᵥ (((1-t) • A+t • B)*ᵥv)=(1-t)*(v ⬝ᵥ (A*ᵥv))+t*(v ⬝ᵥ (B*ᵥv)) := by
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,dotProduct_smul,smul_eq_mul]

lemma endingJoinTensor_bounds {D : Coord3 → Mat3} {lam k J L K c C : ℝ}
    (hD : ∀ x v : Coord3,c*(v ⬝ᵥ v)≤v ⬝ᵥ (D x*ᵥv) ∧ v ⬝ᵥ (D x*ᵥv)≤C*(v ⬝ᵥ v))
    (hE : ∀ x v : Coord3,c*(v ⬝ᵥ v)≤v ⬝ᵥ (alignedEndingTensor lam k J L K x*ᵥv) ∧
      v ⬝ᵥ (alignedEndingTensor lam k J L K x*ᵥv)≤C*(v ⬝ᵥ v)) (x v : Coord3) :
    c*(v ⬝ᵥ v)≤v ⬝ᵥ (endingJoinTensor D lam k J L K x*ᵥv) ∧
      v ⬝ᵥ (endingJoinTensor D lam k J L K x*ᵥv)≤C*(v ⬝ᵥ v) := by
  rw [endingJoinTensor,convexTensor_quadratic]
  have hd := hD x v
  have he := hE (x-Pi.single 0 7) v
  change c*(v ⬝ᵥv)≤v ⬝ᵥ(delayedEndingTensor lam k J L K 7 x*ᵥv) ∧
    v ⬝ᵥ(delayedEndingTensor lam k J L K 7 x*ᵥv)≤C*(v ⬝ᵥv) at he
  have ht := endingJoinCutoff_bounds (x 0)
  have ht' : 0≤1-endingJoinCutoff (x 0) := sub_nonneg.mpr ht.2
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hd.1 ht',mul_le_mul_of_nonneg_left he.1 ht.1]
  · nlinarith [mul_le_mul_of_nonneg_left hd.2 ht',mul_le_mul_of_nonneg_left he.2 ht.1]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_EndingJoinOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real

lemma matchedEndingPair_left_deriv {u : Coord3 → Fin 2 → ℝ} {lam k J L K : ℝ} {x : Coord3}
    (hx : x 0<13/2) :
    fderiv ℝ (matchedEndingPair u lam k J L K) x=fderiv ℝ u x :=
  (axial_paste_eventually_left (f:=u) (g:=axialPair (delayedEndingValue lam k J L K 7))
    (continuous_apply 0) hx).fderiv_eq

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_DelayedPairFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real

lemma delayedPairFlux_C1 {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (j : Fin 2) :
    ContDiff ℝ 1 (delayedPairFlux lam k J L K R j) := by
  unfold delayedPairFlux
  split_ifs
  · exact contDiff_const
  · exact delayedEndingFlux_C1 hJ hL hK

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_MatchedEndingWeak
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Real Matrix
open scoped Matrix.Norms.Elementwise

lemma joinedFlux_C1 {D : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hD : ContDiff ℝ (↑(⊤:ℕ∞)) D) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {lam k J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (j : Fin 2) :
    ContDiff ℝ 1 (joinedFlux D u lam k J L K j) := by
  exact axialFluxBlend_C1 (endingJoinCutoff_smooth.of_le (by simp))
    ((symmetricFlux_smooth hD hu j).of_le (by simp)) (delayedPairFlux_C1 hJ hL hK j)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusLeadingRealMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Real Complex

lemma torusQuadratic_neg_mode (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) :
    torusQuadratic s (-h)=torusQuadratic s h := by
  simp only [torusQuadratic,Pi.neg_apply,Int.cast_neg]
  ring

lemma torusRate_neg_mode (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) :
    torusRate s (-h)=torusRate s h := by
  simp only [torusRate,torusQuadratic_neg_mode]

lemma torusAngular_neg_mode (h : Fin 2 → ℤ) (x : Fin 3 → ℝ) :
    torusAngular (-h) x= -torusAngular h x := by
  simp only [torusAngular,Pi.neg_apply,Int.cast_neg,add_apply,
    smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul]
  ring

lemma polar_real_cosine (c : ℂ) (t : ℝ) :
    ‖c‖*Real.cos (t+c.arg)=c.re*Real.cos t-c.im*Real.sin t := by
  by_cases hc : c=0
  · simp [hc]
  · rw [Real.cos_add,Complex.cos_arg hc,Complex.sin_arg]
    field_simp

lemma realTorusCoeff_neg (f : TorusL2) (h : Fin 2 → ℤ) :
    realTorusCoeff f (-h)=star (realTorusCoeff f h) := by
  simp [realTorusCoeff,star_div₀,star_add,add_comm]

lemma realTorusCoeff_bound (f : TorusL2) (h : Fin 2 → ℤ) :
    ‖realTorusCoeff f h‖≤‖f‖ := by
  unfold realTorusCoeff
  rw [norm_div]
  change ‖mFourierCoeff f h+star (mFourierCoeff f (-h))‖ / ‖(2:ℂ)‖ ≤ ‖f‖

  have hh := norm_add_le (mFourierCoeff f h) (star (mFourierCoeff f (-h)))
  have ha := torusFourierCoeff_bound f h
  have hb := torusFourierCoeff_bound f (-h)
  simp only [norm_star] at hh
  norm_num only [Complex.norm_ofNat] at *
  linarith

lemma realTorusCoeff_polar_mode (s : Fin 3 → ℝ) (f : TorusL2)
    (h : Fin 2 → ℤ) (x : Fin 3 → ℝ) :
    ‖realTorusCoeff f h‖*flatPhaseMode s h (realTorusCoeff f h).arg x=
      (((Real.exp (-torusRate s h*x 0):ℂ)*mFourierCoeff f h*
        Complex.exp ((torusAngular h x:ℂ)*Complex.I)).re+
       ((Real.exp (-torusRate s (-h)*x 0):ℂ)*mFourierCoeff f (-h)*
        Complex.exp ((torusAngular (-h) x:ℂ)*Complex.I)).re)/2 := by
  rw [torusRate_neg_mode,torusAngular_neg_mode]
  rw [complex_mode_real,complex_mode_real]
  simp only [flatPhaseMode,Real.cos_add_pi_div_two,Real.cos_neg,Real.sin_neg]
  rw [←mul_assoc,mul_comm ‖realTorusCoeff f h‖,mul_assoc,polar_real_cosine]
  simp only [realTorusCoeff,Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.add_re,
    Complex.add_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma torusRealContinuation_polar {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : TorusL2) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    torusRealContinuation s f x=
      flatFourier s (fun h => ‖realTorusCoeff f h‖) (fun h => (realTorusCoeff f h).arg) x := by
  let F := fun h : Fin 2 → ℤ =>
    (((Real.exp (-torusRate s h*x 0):ℂ)*mFourierCoeff f h)*
      Complex.exp ((torusAngular h x:ℂ)*Complex.I)).re
  have hc := (ContinuousMap.evalCLM ℂ (torusAngles x)).hasSum
    (poisson_series_norm_summable hs hx f).of_norm.hasSum
  have hr := Complex.reCLM.hasSum hc
  change HasSum (fun h => ((Real.exp (-torusRate s h*x 0):ℂ)*mFourierCoeff f h*
    mFourier h (torusAngles x)).re) (torusRealContinuation s f x) at hr
  simp_rw [mFourier_torusAngles] at hr
  change HasSum F (torusRealContinuation s f x) at hr
  have hn : HasSum (fun h => F (-h)) (torusRealContinuation s f x) :=
    (Equiv.neg (Fin 2 → ℤ)).hasSum_iff.mpr hr
  have hh := (hr.add hn).div_const 2
  have he : (torusRealContinuation s f x+torusRealContinuation s f x)/2=
      torusRealContinuation s f x := by ring
  rw [he] at hh
  exact hh.tsum_eq.symm.trans (by
    unfold flatFourier
    apply tsum_congr
    intro h
    exact (realTorusCoeff_polar_mode s f h x).symm)

lemma realTorusCoeff_zero_re (f : TorusL2) :
    (realTorusCoeff f 0).re=(mFourierCoeff f 0).re := by
  simp only [realTorusCoeff,neg_zero,Complex.div_ofNat_re,Complex.add_re,
    Complex.star_def,Complex.conj_re]
  ring

lemma realTorusCoeff_polar_zero (s : Fin 3 → ℝ) (f : TorusL2) (x : Fin 3 → ℝ) :
    ‖realTorusCoeff f 0‖*flatPhaseMode s 0 (realTorusCoeff f 0).arg x=
      (mFourierCoeff f 0).re := by
  simp [flatPhaseMode,torusRate,torusQuadratic,torusAngular,realTorusCoeff_zero_re]

lemma realTorusCoeff_polar_neg (s : Fin 3 → ℝ) (f : TorusL2)
    (h : Fin 2 → ℤ) (x : Fin 3 → ℝ) :
    ‖realTorusCoeff f (-h)‖*flatPhaseMode s (-h) (realTorusCoeff f (-h)).arg x=
      ‖realTorusCoeff f h‖*flatPhaseMode s h (realTorusCoeff f h).arg x := by
  dsimp only [flatPhaseMode]
  rw [←mul_assoc,mul_comm ‖realTorusCoeff f (-h)‖,mul_assoc,polar_real_cosine,
    ←mul_assoc,mul_comm ‖realTorusCoeff f h‖,mul_assoc,polar_real_cosine,
    torusRate_neg_mode,torusAngular_neg_mode,realTorusCoeff_neg]
  simp [Real.cos_neg,Real.sin_neg]

lemma realTorusAmplitude_bound (f : TorusL2) (h : Fin 2 → ℤ) :
    |realTorusAmplitude f h|≤‖f‖ := by
  unfold realTorusAmplitude
  split_ifs
  · simp
  · simpa only [abs_of_nonneg (norm_nonneg _)] using realTorusCoeff_bound f h

lemma torusRealContinuation_mean_free {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : TorusL2) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    torusRealContinuation s f x=(mFourierCoeff f 0).re+
      flatFourier s (realTorusAmplitude f) (realTorusPhase f) x := by
  classical
  rw [torusRealContinuation_polar hs f hx]
  have hb (h) : |‖realTorusCoeff f h‖|≤‖f‖ := by
    simpa only [abs_of_nonneg (norm_nonneg _)] using realTorusCoeff_bound f h
  rw [flatFourier,(flatFourier_summable hs hb hx).tsum_eq_add_tsum_ite 0,
    realTorusCoeff_polar_zero]
  congr 1
  unfold flatFourier
  apply tsum_congr
  intro h
  simp only [realTorusAmplitude,realTorusPhase]
  split_ifs <;> simp

lemma torusRate_uniform_positive {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    ∃ g>0,∀ h : Fin 2 → ℤ,h≠0 → g≤torusRate s h := by
  have he : ({h : Fin 2 → ℤ | h≠0} : Set (Fin 2 → ℤ)).Nonempty := by
    refine ⟨![1,0],?_⟩
    intro he
    have := congrFun he 0
    norm_num at this
  obtain ⟨h,hh,hmin⟩ := torus_modes_have_first hs he
  refine ⟨torusRate s h,Real.sqrt_pos.mpr (torusQuadratic_pos hs hh),?_⟩
  intro l hl
  exact Real.sqrt_le_sqrt (hmin l hl)

lemma torus_leading_rate_gap {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hres : ∀ h l : Fin 2 → ℤ,torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h)
    {M : Set (Fin 2 → ℤ)} (hne : M.Nonempty) (hzero : 0∉M) :
    ∃ h∈M,0<torusRate s h ∧ ∃ g>0,
      ∀ l∈M,l≠h → l≠-h → torusRate s h+g≤torusRate s l := by
  obtain ⟨h,hh,hq,d,hd,hmin⟩ := torus_leading_pair_gap hs hres hne hzero
  refine ⟨h,hh,Real.sqrt_pos.mpr hq,Real.sqrt (torusQuadratic s h+d)-torusRate s h,
    sub_pos.mpr (Real.sqrt_lt_sqrt hq.le (by linarith)),?_⟩
  intro l hl hne hn
  have hle := Real.sqrt_le_sqrt (hmin l hl hne hn)
  change Real.sqrt (torusQuadratic s h)+(Real.sqrt (torusQuadratic s h+d)-
    Real.sqrt (torusQuadratic s h))≤Real.sqrt (torusQuadratic s l)
  linarith

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierPairFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma flatFourier_const_mul (s : Fin 3 → ℝ) (a phase : (Fin 2 → ℤ) → ℝ) (c : ℝ) (x : Coord3) :
    flatFourier s (fun h => c*a h) phase x=c*flatFourier s a phase x := by
  simp only [flatFourier,mul_assoc,tsum_mul_left]

lemma flatFourier_translation (s : Fin 3 → ℝ) (a phase : (Fin 2 → ℤ) → ℝ) (T : ℝ) (x : Coord3) :
    flatFourier s a phase (x+![T,0,0])=
      flatFourier s (fun h => a h*exp (-torusRate s h*T)) phase x := by
  unfold flatFourier
  apply tsum_congr
  intro h
  rw [flatPhaseMode_translation]
  ring

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma flatFourier_normalized_translation (s : Fin 3 → ℝ) (lam T : ℝ)
    (a phase : (Fin 2 → ℤ) → ℝ) (x : Coord3) :
    flatFourier s (normalizedFourierCoefficients s lam T a) phase x=
      exp (lam*T)*flatFourier s a phase (x+![T,0,0]) := by
  rw [flatFourier_translation,←flatFourier_const_mul]
  unfold flatFourier
  apply tsum_congr
  intro h
  have he : exp (-(torusRate s h-lam)*T)=exp (lam*T)*exp (-torusRate s h*T) := by
    rw [←exp_add]
    congr 1
    ring
  simp only [normalizedFourierCoefficients,he]
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierMatchingFamilyCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real Matrix
open scoped Matrix.Norms.Elementwise

lemma axial_torusRate_pos {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : k≠0) : 0<torusRate s ![0,k] := by
  have hb := torusRate_lower hs ![0,k]
  have hk' : (k:ℝ)≠0 := by exact_mod_cast hk
  have hp := abs_pos.mpr hk'
  simp only [torusSize,Matrix.cons_val_zero,Matrix.cons_val_one,Int.cast_zero,abs_zero,zero_add] at hb
  linarith

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndingJoinPeriodicity
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma delayedEndingTensor_periodic (lam J L K R : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (delayedEndingTensor lam k J L K R) := by
  intro n x
  change alignedEndingTensor lam k J L K (x+angularShift (2*Real.pi) n-Pi.single 0 R)=_
  rw [add_sub_right_comm,alignedEndingTensor_angularPeriodic]
  rfl

lemma endingJoinTensor_periodic {D : Coord3 → Mat3}
    (hD : AngularPeriodic (2*Real.pi) D) (lam J L K : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (endingJoinTensor D lam k J L K) := by
  intro n x
  have ht : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  simp only [endingJoinTensor,ht,hD n x,delayedEndingTensor_periodic _ _ _ _ _ _ n x]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierFiniteEndingNormal
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Real Matrix
open scoped Matrix.Norms.Elementwise

attribute [local instance] OAI.ScalarConductivity.fourierFiniteEndingNormalMeasurableSpace
local instance fourierFiniteEndingNormalBorelSpace_rceb1e7_1 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))
theorem aligned_fourier_finite_ending_with_normal {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : 0<k) {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s ![0,k]+gb≤torusRate s h)
    (hpb : pb ![0,k]=0) {δ : ℝ} (hδ : 0<δ) :
    ∃ p T c C : ℝ,p∈Ioc 0 (1/2) ∧ p<δ ∧ 7<T ∧ 0 < c ∧ c≤C ∧
      ∃ (v : Coord3 → Fin 2 → ℝ) (E : Coord3 → Mat3),
        ContDiff ℝ 2 v ∧ Measurable E ∧
        AngularPeriodic (2*Real.pi) v ∧ AngularPeriodic (2*Real.pi) E ∧
        (∃ hsym : ∀ x,(E x).IsSymm,
          ∀ᵐ x : Coord3,0<x 0 → x∈regularRegion v (fun y => ⟨E y,hsym y⟩) {y : Coord3 | 0<y 0}) ∧
        (∀ x w,c*(w ⬝ᵥ w)≤w ⬝ᵥ (E x*ᵥw) ∧ w ⬝ᵥ (E x*ᵥw)≤C*(w ⬝ᵥ w)) ∧
        (∀ x,x 0∈Icc 0 (1/2) → v x=
          ![x 0+flatFourier s (normalizedFourierCoefficients s 0 (10+1/p) a) pa x,
            flatPhaseMode s ![0,k] 0 x+
              flatFourier s (normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b) pb x]) ∧
        (∀ x,x 0∈Icc 0 (1/2) → E x=flatBackgroundTensor s) ∧
        (∀ x,T≤x 0 → v x=![x 0,0]) ∧
        (∀ x,7≤x 0 → E x*ᵥPi.single 0 1=Pi.single 0 1) ∧
        (∀ᵐ x : Coord3,x 0∈Ioo 0 6 → LinearIndependent ℝ (gradientColumns (fderiv ℝ v x)).col) ∧
        (∃ G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ, ContDiff ℝ 1 G ∧
          ∀ᵐ x : Coord3,E x*gradientColumns (fderiv ℝ v x)=G x) ∧
        ∀ (j : Fin 2) (ψ : SmoothScalar Coord3),HasCompactSupport ψ.val →
          tsupport ψ.val ⊆ {x : Coord3 | 0<x 0} →
          Integrable (fun x => ∑ i,(E x*gradientColumns (fderiv ℝ v x)).col j i*
            (smoothDirection (Pi.single i 1) ψ).val x) ∧
          (∫ x,∑ i,(E x*gradientColumns (fderiv ℝ v x)).col j i*
            (smoothDirection (Pi.single i 1) ψ).val x)=0 := by
  have hk0 : k≠0 := ne_of_gt hk
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  let lam := torusRate s ![0,k]
  have hlam : 0<lam := axial_torusRate_pos hs hk0
  obtain ⟨p,hp,hpδ,u,D,hus,hDs,hup,hDp,hDsym,hDb,hPDE,hDflat,huin,huout,hurank⟩ :=
    elliptic_fourier_matching_regular (pa:=pa) hs hk0 hA hB ha hb hga hgb hra hrb hpb hδ
  obtain ⟨J,L,K,ce,Ce,hJ,hL,hK,hce,hceCe,he⟩ := exists_finiteEnding_parameters (div_pos hlam hkr)
  let c := min (1/4) ce
  let C := max (3*‖flatBackgroundTensor s‖+1) Ce
  let T := 7+(J+2+2*cascadeLength L K)/(k:ℝ)
  have hl : 0 < cascadeLength L K := cascade_length_positive (by linarith) hK
  have hT : 7<T := by dsimp [T]; linarith [div_pos (show 0<J+2+2*cascadeLength L K by linarith) hkr]
  have hum : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos ((k:ℝ)*x 2)] := by
    intro x hx
    rw [huout x hx]
    congr 1
    simp [flatPhaseMode,torusAngular,lam]
  have hDm : ∀ x : Coord3,x 0∈Icc (6:ℝ) 7 → D x=flatBackgroundTensor s := by
    intro x hx
    apply hDflat x
    intro hh
    linarith [hh.2,hx.1]
  have hDb' : ∀ x w : Coord3,c*(w ⬝ᵥ w)≤w ⬝ᵥ(D x*ᵥw) ∧ w ⬝ᵥ(D x*ᵥw)≤C*(w ⬝ᵥ w) := by
    intro x w
    have hw : 0≤w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hw).trans (hDb x w).1,
      (hDb x w).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw)⟩
  have he' : ∀ x w : Coord3,c*(w ⬝ᵥ w)≤w ⬝ᵥ(alignedEndingTensor lam k J L K x*ᵥw) ∧
      w ⬝ᵥ(alignedEndingTensor lam k J L K x*ᵥw)≤C*(w ⬝ᵥ w) := by
    intro x w
    have hw : 0≤w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have hh := alignedEndingTensor_bounds he x w
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) hw).trans hh.1,
      hh.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw)⟩
  have hDmeas : Measurable D := by
    apply Measurable.of_eval; intro i
    apply Measurable.of_eval; intro j
    exact ((continuous_apply j).comp ((continuous_apply i).comp hDs.continuous)).measurable
  refine ⟨p,T,c,C,hp,hpδ,hT,lt_min (by norm_num) hce,
    (min_le_right _ _).trans (hceCe.trans (le_max_right _ _)),
    matchedEndingPair u lam k J L K,endingJoinTensor D lam k J L K,
    matchedEndingPair_C2 (hus.of_le (show (2:WithTop ℕ∞)≤↑(⊤:ℕ∞) by norm_cast)) hkr hJ hL hK hum,
    endingJoinTensor_measurable hDmeas _ _ _ _ _,
    matchedEndingPair_periodic hup _ _ _ _ _,endingJoinTensor_periodic hDp _ _ _ _ _,
    ?_,endingJoinTensor_bounds hDb' he',?_,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨endingJoinTensor_symm hDsym _ _ _ _ _,?_⟩
    exact matchedEnding_regularRegion_ae hDs hus hDsym hkr hJ (by linarith) hK hum hDm hurank
      (isOpen_lt continuous_const (continuous_apply 0)) (Subset.refl _)
  · intro x hx
    rw [matchedEndingPair,ite_eq_left (by linarith [hx.2])]
    exact huin x hx
  · intro x hx
    rw [endingJoinTensor_left _ _ _ _ _ _ _ (by linarith [hx.2])]
    by_cases hh : x 0<1/2
    · exact hDflat x (fun h => (not_le.mpr hh) h.1)
    have heq : x 0=1/2 := le_antisymm hx.2 (le_of_not_gt hh)

    have hnear : ∀ᶠ y in 𝓝[<] (1/2:ℝ),D (Function.update x 0 y)=flatBackgroundTensor s := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      apply hDflat
      simpa using (show y∉Icc (1/2:ℝ) (11/2) from fun h => (not_le.mpr hy) h.1)
    have hlim : Tendsto (fun y : ℝ => D (Function.update x 0 y)) (𝓝[<] (1/2:ℝ)) (𝓝 (D x)) := by
      have hupp : Continuous (fun y : ℝ => Function.update x 0 y) := by
        apply continuous_pi
        intro i
        by_cases hi : i=0
        · subst i
          change Continuous (fun y : ℝ => y)
          exact continuous_id
        · simpa [Function.update_of_ne hi] using (continuous_const : Continuous (fun _ : ℝ => x i))
      have hc : Continuous (fun y : ℝ => D (Function.update x 0 y)) := hDs.continuous.comp hupp
      have := (hc.tendsto (1/2)).mono_left (nhdsWithin_le_nhds (s:=Iio (1/2:ℝ)))
      simpa only [←heq,Function.update_eq_self] using this
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hnear))
  · intro x hx
    apply matchedEndingPair_terminal hJ hL hK x (by linarith)
    have hh : (J+2+2*cascadeLength L K)/(k:ℝ)≤x 0-7 := by dsimp [T] at hx; linarith
    simpa only [mul_comm] using (div_le_iff₀ hkr).mp hh
  · intro x hx
    rw [endingJoinTensor_right _ _ _ _ _ _ _ hx]
    exact alignedEndingTensor_normal _ _ _ _ _ _
  · filter_upwards [hurank] with x hx
    intro hbnd
    rw [matchedEndingPair_left_deriv (by linarith [hbnd.2])]
    exact hx hbnd
  · refine ⟨(fun x i j => joinedFlux D u lam k J L K j x i),?_,?_⟩
    · exact contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j =>
        contDiff_pi.mp (joinedFlux_C1 hDs hus hJ hL hK j) i))
    · filter_upwards [endingJoin_constitution_ae (D:=D) hkr hJ hL hK hum] with x hx
      ext i j
      exact congrFun (hx j) i
  · intro j ψ hcψ hsψ
    exact matchedEnding_weak_equation hDs hus hkr hJ hL hK hum hDm hPDE j ψ hcψ hsψ

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_LeadingFrequencyAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

theorem leading_frequency_SL2_alignment {h : Fin 2 → ℤ} (hh : h≠0) :
    ∃ (k : ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ),
      0<k ∧ A.det=1 ∧ h ᵥ* A=![0,k] := by
  have hg : 0<Int.gcd (h 0) (h 1) := by
    apply Nat.pos_of_ne_zero
    intro he
    have hz := Int.gcd_eq_zero_iff.mp he
    apply hh
    ext i
    fin_cases i
    · exact hz.1
    · exact hz.2
  obtain ⟨u,v,huv,h0,h1⟩ := Int.exists_gcd_one hg
  let a := Int.gcdA u v
  let b := Int.gcdB u v
  have hab : u*a+v*b=1 := by
    simpa only [huv,Int.natCast_one] using (Int.gcd_eq_gcd_ab u v).symm
  refine ⟨Int.gcd (h 0) (h 1),!![v,a;-u,b],by exact_mod_cast hg,?_,?_⟩
  · rw [Matrix.det_fin_two_of]
    nlinarith
  · ext i
    fin_cases i
    · simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
        Matrix.cons_val_zero,Matrix.cons_val_one]
      change h 0*v+h 1*(-u)=0
      calc
        _ = (u*(Int.gcd (h 0) (h 1):ℤ))*v+(v*(Int.gcd (h 0) (h 1):ℤ))*(-u) :=
          congrArg₂ (fun x y : ℤ => x*v+y*(-u)) h0 h1
        _ = 0 := by ring
    · simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
        Matrix.cons_val_zero,Matrix.cons_val_one]
      change h 0*a+h 1*b=(Int.gcd (h 0) (h 1):ℤ)
      calc
        _ = (u*a+v*b)*(Int.gcd (h 0) (h 1):ℤ) := by
          calc
            _ = (u*(Int.gcd (h 0) (h 1):ℤ))*a+(v*(Int.gcd (h 0) (h 1):ℤ))*b :=
              congrArg₂ (fun x y : ℤ => x*a+y*b) h0 h1
            _ = _ := by ring
        _ = _ := by rw [hab,one_mul]

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma twoCoordinate_cauchy (a b x y : ℝ) :
    (a*x+b*y)^2≤(a^2+b^2)*(x^2+y^2) := by
  nlinarith [sq_nonneg (a*y-b*x)]

theorem normalizedAngularTensor_lower {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) (x y : ℝ) :
    (1/2)*(x^2+y^2)≤normalizedAngularTensor s A 0*x^2+
      2*normalizedAngularTensor s A 1*x*y+normalizedAngularTensor s A 2*y^2 := by
  let a : ℝ := A 0 0
  let b : ℝ := A 0 1
  let c : ℝ := A 1 0
  let d : ℝ := A 1 1
  let M := angularNormalization A
  have hdZ : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using hA
  have hd : a*d-b*c=1 := by
    dsimp [a,b,c,d]
    exact_mod_cast hdZ
  let u := d*x-c*y
  let v := -b*x+a*y
  have hx : a*u+c*v=x := by
    calc
      _ = (a*d-b*c)*x := by dsimp [u,v]; ring
      _ = _ := by rw [hd,one_mul]
  have hy : b*u+d*v=y := by
    calc
      _ = (a*d-b*c)*y := by dsimp [u,v]; ring
      _ = _ := by rw [hd,one_mul]
  have hn : x^2+y^2≤M*(u^2+v^2) := by
    calc
      _ = (a*u+c*v)^2+(b*u+d*v)^2 := by rw [hx,hy]
      _ ≤ (a^2+c^2)*(u^2+v^2)+(b^2+d^2)*(u^2+v^2) :=
        add_le_add (twoCoordinate_cauchy a c u v) (twoCoordinate_cauchy b d u v)
      _ ≤ M*(u^2+v^2) := by
        dsimp [M,angularNormalization,a,b,c,d]
        nlinarith [sq_nonneg u,sq_nonneg v]
  have he : normalizedAngularTensor s A 0*x^2+
      2*normalizedAngularTensor s A 1*x*y+normalizedAngularTensor s A 2*y^2=
      M*(s 0*u^2+2*s 1*u*v+s 2*v^2) := by
    dsimp [normalizedAngularTensor,M,u,v,a,b,c,d]
    ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left (hs u v) (angularNormalization_pos A).le
  nlinarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularFourierConjugacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma normalizedAngularTensor_quadratic (s : Fin 3 → ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℝ) :
    normalizedAngularTensor s A 0*x^2+2*normalizedAngularTensor s A 1*x*y+
      normalizedAngularTensor s A 2*y^2=
      angularNormalization A *
        (s 0*((A 1 1:ℝ)*x-(A 1 0:ℝ)*y)^2+
          2*s 1*((A 1 1:ℝ)*x-(A 1 0:ℝ)*y)*(-(A 0 1:ℝ)*x+(A 0 0:ℝ)*y)+
          s 2*(-(A 0 1:ℝ)*x+(A 0 0:ℝ)*y)^2) := by
  dsimp [normalizedAngularTensor]
  ring

lemma angular_vecMul_zero (h : Fin 2 → ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ((h ᵥ* A) 0:ℝ)=(h 0:ℝ)*(A 0 0:ℝ)+(h 1:ℝ)*(A 1 0:ℝ) := by
  simp [Matrix.vecMul,dotProduct,Fin.sum_univ_two]

lemma angular_vecMul_one (h : Fin 2 → ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ((h ᵥ* A) 1:ℝ)=(h 0:ℝ)*(A 0 1:ℝ)+(h 1:ℝ)*(A 1 1:ℝ) := by
  simp [Matrix.vecMul,dotProduct,Fin.sum_univ_two]

lemma angular_vecMul_inverse {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (h : Fin 2 → ℤ) :
    (A 1 1:ℝ)*((h ᵥ* A) 0:ℝ)-(A 1 0:ℝ)*((h ᵥ* A) 1:ℝ)=(h 0:ℝ) ∧
    -(A 0 1:ℝ)*((h ᵥ* A) 0:ℝ)+(A 0 0:ℝ)*((h ᵥ* A) 1:ℝ)=(h 1:ℝ) := by
  have hdZ : A 0 0*A 1 1-A 0 1*A 1 0=1 := by simpa only [det_fin_two] using hA
  have hd : (A 0 0:ℝ)*(A 1 1:ℝ)-(A 0 1:ℝ)*(A 1 0:ℝ)=1 := by exact_mod_cast hdZ
  rw [angular_vecMul_zero,angular_vecMul_one]
  constructor
  · calc
      _ = ((A 0 0:ℝ)*(A 1 1:ℝ)-(A 0 1:ℝ)*(A 1 0:ℝ))*(h 0:ℝ) := by ring
      _ = _ := by rw [hd,one_mul]
  · calc
      _ = ((A 0 0:ℝ)*(A 1 1:ℝ)-(A 0 1:ℝ)*(A 1 0:ℝ))*(h 1:ℝ) := by ring
      _ = _ := by rw [hd,one_mul]

lemma torusQuadratic_angular_conjugacy (s : Fin 3 → ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) (h : Fin 2 → ℤ) :
    torusQuadratic (normalizedAngularTensor s A) (h ᵥ* A)=
      angularNormalization A*torusQuadratic s h := by
  unfold torusQuadratic
  rw [normalizedAngularTensor_quadratic,(angular_vecMul_inverse hA h).1,
    (angular_vecMul_inverse hA h).2]

lemma torusRate_angular_conjugacy (s : Fin 3 → ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) (h : Fin 2 → ℤ) :
    torusRate (normalizedAngularTensor s A) (h ᵥ* A)=
      Real.sqrt (angularNormalization A)*torusRate s h := by
  unfold torusRate
  rw [torusQuadratic_angular_conjugacy s hA,
    Real.sqrt_mul (angularNormalization_pos A).le]

lemma torusAngular_normalizedLift (h : Fin 2 → ℤ)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (x : Coord3) :
    torusAngular h (angularNormalizedLift A x)=torusAngular (h ᵥ* A) x := by
  simp only [torusAngular,_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul]
  rw [angular_vecMul_zero,angular_vecMul_one]
  dsimp [angularNormalizedLift]
  ring

theorem flatPhaseMode_angular_conjugacy (s : Fin 3 → ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (h : Fin 2 → ℤ) (phase : ℝ) (x : Coord3) :
    flatPhaseMode s h phase (angularNormalizedLift A x)=
      flatPhaseMode (normalizedAngularTensor s A) (h ᵥ* A) phase x := by
  unfold flatPhaseMode
  rw [torusAngular_normalizedLift,torusRate_angular_conjugacy s hA]
  congr 2
  dsimp [angularNormalizedLift]
  ring

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

theorem flatFourier_angular_conjugacy (s : Fin 3 → ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (a phase : (Fin 2 → ℤ) → ℝ) (x : Coord3) :
    flatFourier s a phase (angularNormalizedLift A x)=
      flatFourier (normalizedAngularTensor s A)
        (a ∘ (angularFrequencyEquiv A hA).symm)
        (phase ∘ (angularFrequencyEquiv A hA).symm) x := by
  unfold flatFourier
  conv_rhs => rw [←(angularFrequencyEquiv A hA).tsum_eq]
  apply tsum_congr
  intro h
  simp only [Function.comp_apply,angularFrequencyEquiv_apply,angularFrequencyEquiv_symm_vecMul]
  rw [flatPhaseMode_angular_conjugacy s hA]

lemma normalizedFourierCoefficients_angular_conjugacy (s : Fin 3 → ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (a : (Fin 2 → ℤ) → ℝ) (lam T : ℝ) (h : Fin 2 → ℤ) :
    normalizedFourierCoefficients (normalizedAngularTensor s A)
      (Real.sqrt (angularNormalization A)*lam) T
      (a ∘ (angularFrequencyEquiv A hA).symm) (angularFrequencyEquiv A hA h)=
    normalizedFourierCoefficients s lam (Real.sqrt (angularNormalization A)*T) a h := by
  simp only [normalizedFourierCoefficients,Function.comp_apply,
    angularFrequencyEquiv_apply,angularFrequencyEquiv_symm_vecMul,torusRate_angular_conjugacy s hA]
  congr 2
  ring

lemma angular_conjugacy_gap (s : Fin 3 → ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    {a : (Fin 2 → ℤ) → ℝ} {lam gap : ℝ}
    (hgap : 0<gap) (hr : ∀ h,a h≠0 → lam+gap≤torusRate s h) :
    0<Real.sqrt (angularNormalization A)*gap ∧
      ∀ h,(a ∘ (angularFrequencyEquiv A hA).symm) h≠0 →
        Real.sqrt (angularNormalization A)*lam+Real.sqrt (angularNormalization A)*gap≤
          torusRate (normalizedAngularTensor s A) h := by
  have hm : 0<Real.sqrt (angularNormalization A) := Real.sqrt_pos.mpr (angularNormalization_pos A)
  refine ⟨mul_pos hm hgap,?_⟩
  intro h hh
  obtain ⟨g,rfl⟩ := (angularFrequencyEquiv A hA).surjective h
  simp only [Function.comp_apply,Equiv.symm_apply_apply] at hh
  rw [angularFrequencyEquiv_apply,torusRate_angular_conjugacy s hA]
  simpa only [mul_add] using mul_le_mul_of_nonneg_left (hr g hh) hm.le

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularPhaseTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma flatPhaseMode_angular_translation (s : Fin 3 → ℝ) (h : Fin 2 → ℤ)
    (phase : ℝ) (v : Fin 2 → ℝ) (x : Coord3) :
    flatPhaseMode s h phase (angularRealTranslation v x)=
      flatPhaseMode s h (phase+(h 0:ℝ)*v 0+(h 1:ℝ)*v 1) x := by
  unfold flatPhaseMode
  congr 1
  congr 1
  simp only [torusAngular,_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul]
  dsimp [angularRealTranslation]
  ring

theorem flatFourier_angular_translation (s : Fin 3 → ℝ)
    (a phase : (Fin 2 → ℤ) → ℝ) (v : Fin 2 → ℝ) (x : Coord3) :
    flatFourier s a phase (angularRealTranslation v x)=
      flatFourier s a (angularShiftPhase phase v) x := by
  unfold flatFourier
  apply tsum_congr
  intro h
  rw [flatPhaseMode_angular_translation]
  rfl

lemma alignedPhaseTranslation_zero {k : ℤ} (hk : 0<k) (phase : ℝ) :
    phase+((![0,k] : Fin 2 → ℤ) 0:ℝ)*((![0,-phase/(k:ℝ)] : Fin 2 → ℝ) 0)+
      ((![0,k] : Fin 2 → ℤ) 1:ℝ)*((![0,-phase/(k:ℝ)] : Fin 2 → ℝ) 1)=0 := by
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  simp only [cons_val_zero,cons_val_one,Int.cast_zero,zero_mul,add_zero]
  field_simp
  ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_GeneralModeEndingScalarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma flatFourier_div_coefficients (s : Fin 3 → ℝ)
    (a phase : (Fin 2 → ℤ) → ℝ) (d : ℝ) (x : Coord3) :
    flatFourier s (fun h => a h/d) phase x=flatFourier s a phase x/d := by
  unfold flatFourier
  simp_rw [div_mul_eq_mul_div]
  exact tsum_div_const

lemma normalizedFourierCoefficients_div (s : Fin 3 → ℝ) (lam T d : ℝ)
    (a : (Fin 2 → ℤ) → ℝ) :
    normalizedFourierCoefficients s lam T (fun h => a h/d)=
      fun h => normalizedFourierCoefficients s lam T a h/d := by
  funext h
  unfold normalizedFourierCoefficients
  ring

lemma normalized_flatFourier_angular_conjugacy (s : Fin 3 → ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (a phase : (Fin 2 → ℤ) → ℝ) (lam T : ℝ) (θ : Fin 2 → ℝ) (x : Coord3) :
    flatFourier (normalizedAngularTensor s A)
      (normalizedFourierCoefficients (normalizedAngularTensor s A)
        (Real.sqrt (angularNormalization A)*lam) T
        (a ∘ (angularFrequencyEquiv A hA).symm))
      (angularShiftPhase (phase ∘ (angularFrequencyEquiv A hA).symm) θ) x=
    flatFourier s (normalizedFourierCoefficients s lam
      (Real.sqrt (angularNormalization A)*T) a) phase
      (angularNormalizedLift A (angularRealTranslation θ x)) := by
  rw [flatFourier_angular_conjugacy s hA,flatFourier_angular_translation]
  congr 1
  funext h
  obtain ⟨g,rfl⟩ := (angularFrequencyEquiv A hA).surjective h
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using
    normalizedFourierCoefficients_angular_conjugacy s hA a lam T g

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_GeneralModeFiniteEndNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

attribute [local instance] OAI.ScalarConductivity.generalModeFiniteEndNormalMeasurableSpace
local instance generalModeFiniteEndNormalBorelSpace_rceb1e7_1 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))
theorem general_mode_finite_ending_raw_normal {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {h₀ : Fin 2 → ℤ} (hh₀ : h₀≠0)
    {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s h₀+gb≤torusRate s h)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ) (k : ℤ),
      Q.det=1 ∧ 0<k ∧ h₀ ᵥ* Q=![0,k] ∧
      ∃ p T c C : ℝ,p∈Ioc 0 (1/2) ∧ p<δ ∧ 7<T ∧ 0 < c ∧ c≤C ∧
      ∃ (v : Coord3 → Fin 2 → ℝ) (E : Coord3 → Mat3)
        (hsym : ∀ x,(E x).IsSymm),
        ContDiff ℝ 2 v ∧ Measurable E ∧
        AngularPeriodic (2*Real.pi) v ∧ AngularPeriodic (2*Real.pi) E ∧
        (∀ x w,c*(w ⬝ᵥ w)≤w ⬝ᵥ (E x*ᵥw) ∧ w ⬝ᵥ (E x*ᵥw)≤C*(w ⬝ᵥ w)) ∧
        (∀ x,x 0∈Icc 0 (1/2) → v x=
          ![x 0+flatFourier s (normalizedFourierCoefficients s 0
              (Real.sqrt (angularNormalization Q)*(10+1/p)) a) pa
              (angularNormalizedLift Q (angularRealTranslation θ x))/Real.sqrt (angularNormalization Q),
            flatPhaseMode s h₀ (pb h₀) (angularNormalizedLift Q (angularRealTranslation θ x))+
              flatFourier s (normalizedFourierCoefficients s (torusRate s h₀)
                (Real.sqrt (angularNormalization Q)*(10+1/p)) b) pb
                (angularNormalizedLift Q (angularRealTranslation θ x))]) ∧
        (∀ x,x 0∈Icc 0 (1/2) → E x=flatBackgroundTensor (normalizedAngularTensor s Q)) ∧
        (∀ x,T≤x 0 → v x=![x 0,0]) ∧
        (∀ x,7≤x 0 → E x*ᵥPi.single 0 1=Pi.single 0 1) ∧
        (∀ᵐ x : Coord3,0<x 0 → x∈regularRegion v (fun y => ⟨E y,hsym y⟩) {y : Coord3 | 0<y 0}) ∧
        (∃ G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ, ContDiff ℝ 1 G ∧
          ∀ᵐ x : Coord3,E x*gradientColumns (fderiv ℝ v x)=G x) ∧
        ∀ (j : Fin 2) (ψ : SmoothScalar Coord3),HasCompactSupport ψ.val →
          tsupport ψ.val ⊆ {x : Coord3 | 0<x 0} →
          Integrable (fun x => ∑ i,(E x*gradientColumns (fderiv ℝ v x)).col j i*
            (smoothDirection (Pi.single i 1) ψ).val x) ∧
          (∫ x,∑ i,(E x*gradientColumns (fderiv ℝ v x)).col j i*
            (smoothDirection (Pi.single i 1) ψ).val x)=0 := by
  obtain ⟨k,Q,hk,hQ,he⟩ := leading_frequency_SL2_alignment hh₀
  let m := Real.sqrt (angularNormalization Q)
  have hm : 0 < m := Real.sqrt_pos.mpr (angularNormalization_pos Q)
  let e := angularFrequencyEquiv Q hQ
  let θ : Fin 2 → ℝ := ![0,-pb h₀/(k:ℝ)]
  let a' : (Fin 2 → ℤ) → ℝ := fun h => a (e.symm h)/m
  let b' : (Fin 2 → ℤ) → ℝ := b ∘ e.symm
  let pa' := angularShiftPhase (pa ∘ e.symm) θ
  let pb' := angularShiftPhase (pb ∘ e.symm) θ
  have hphase : pb' ![0,k]=0 := by
    have he0 : e.symm ![0,k]=h₀ := by
      rw [←he]
      exact e.symm_apply_apply h₀
    dsimp [pb',angularShiftPhase]
    rw [he0]
    exact alignedPhaseTranslation_zero hk (pb h₀)
  have hmode (x : Coord3) :
      flatPhaseMode s h₀ (pb h₀) (angularNormalizedLift Q (angularRealTranslation θ x))=
      flatPhaseMode (normalizedAngularTensor s Q) ![0,k] 0 x := by
    rw [flatPhaseMode_angular_conjugacy s hQ,he,flatPhaseMode_angular_translation]
    rw [show pb h₀+((![0,k] : Fin 2 → ℤ) 0:ℝ)*θ 0+
      ((![0,k] : Fin 2 → ℤ) 1:ℝ)*θ 1=0 from alignedPhaseTranslation_zero hk (pb h₀)]
  have hab : ∀ h,|a' h|≤A/m := by
    intro h
    dsimp [a']
    rw [abs_div,abs_of_pos hm]
    exact (div_le_div_iff_of_pos_right hm).2 (ha _)
  have hbb : ∀ h,|b' h|≤B := fun h => hb (e.symm h)
  have hgapA := angular_conjugacy_gap s hQ (a:=a) (lam:=0) hga
    (fun h hh => by simpa only [zero_add] using hra h hh)
  have hgapB := angular_conjugacy_gap s hQ hgb hrb
  have hrate : torusRate (normalizedAngularTensor s Q) ![0,k]=m*torusRate s h₀ := by
    rw [←he,torusRate_angular_conjugacy s hQ]
  have hra' : ∀ h,a' h≠0 → m*ga≤torusRate (normalizedAngularTensor s Q) h := by
    intro h hh
    have hh' : (a ∘ e.symm) h≠0 := by
      intro hz
      apply hh
      dsimp [a']
      rw [show a (e.symm h)=0 from hz,zero_div]
    simpa only [mul_zero,zero_add] using hgapA.2 h hh'
  have hrb' : ∀ h,b' h≠0 → torusRate (normalizedAngularTensor s Q) ![0,k]+m*gb≤
      torusRate (normalizedAngularTensor s Q) h := by
    intro h hh
    rw [hrate]
    exact hgapB.2 h hh
  obtain ⟨p,T,c,C,hp,hpδ,hT,hc,hcC,v,E,hv,hEm,hvp,hEp,⟨hsym,hreg⟩,hbound,hvin,hEin,hterm,hnormal,_hrank,hG,hpde⟩ :=
    aligned_fourier_finite_ending_with_normal (pa:=pa')
      (normalizedAngularTensor_lower hs hQ) hk (div_nonneg hA hm.le) hB hab hbb
      (mul_pos hm hga) (mul_pos hm hgb) hra' hrb' hphase hδ
  refine ⟨Q,θ,k,hQ,hk,he,p,T,c,C,hp,hpδ,hT,hc,hcC,v,E,hsym,hv,hEm,hvp,hEp,hbound,?_,hEin,hterm,hnormal,hreg,hG,hpde⟩
  intro x hx
  rw [hvin x hx,hmode]
  congr 1
  · congr 1
    rw [normalizedFourierCoefficients_div,flatFourier_div_coefficients]
    congr 1
    simpa only [pa',e,Function.comp_def,mul_zero] using normalized_flatFourier_angular_conjugacy s hQ a pa 0 (10+1/p) θ x
  · rw [hrate]
    congr 2
    simpa only [b',pb',m,e,Function.comp_apply] using normalized_flatFourier_angular_conjugacy s hQ b pb (torusRate s h₀) (10+1/p) θ x

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma operatorMatrix_angularNormalizedEquiv (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det=1) :
    operatorMatrix (angularNormalizedEquiv A hA : Coord3 →L[ℝ] Coord3)=angularLiftMatrix A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorMatrix,angularLiftMatrix,angularNormalizedEquiv,angularNormalizedLinear,
      angularNormalizedLift]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularInverseTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma angularLiftMatrix_background {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (s : Fin 3 → ℝ) :
    angularLiftMatrix A*flatBackgroundTensor (normalizedAngularTensor s A)*(angularLiftMatrix A)ᵀ=
      angularNormalization A • flatBackgroundTensor s := by
  have hd := congrArg (fun z : ℝ => z^2) (real_angular_det_one hA)
  norm_num only [one_pow] at hd
  have hm := Real.sq_sqrt (angularNormalization_pos A).le
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_three,Matrix.transpose_apply,
      angularLiftMatrix,flatBackgroundTensor,normalizedAngularTensor]
  · nlinarith [hm]
  · linear_combination angularNormalization A * s 0 * hd
  · linear_combination angularNormalization A * s 1 * hd
  · linear_combination angularNormalization A * s 1 * hd
  · linear_combination angularNormalization A * s 2 * hd

lemma angularInverseLift_shift (A : Matrix (Fin 2) (Fin 2) ℤ)
    (T : ℝ) (n : Fin 2 → ℤ) (x : Coord3) :
    angularInverseLift A (x+angularShift T n)=angularInverseLift A x+
      angularShift T ![A 1 1*n 0-A 0 1*n 1,-A 1 0*n 0+A 0 0*n 1] := by
  ext i
  fin_cases i <;> simp [angularInverseLift,angularShift] <;> ring

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real
open scoped Matrix.Norms.Elementwise

lemma undoAngularPoint_forward {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (θ : Fin 2 → ℝ) (d : ℝ) (x : Coord3) :
    angularNormalizedLift A (angularRealTranslation θ (undoAngularPoint A θ d x))=x-![d,0,0] := by
  have he : angularRealTranslation θ (undoAngularPoint A θ d x)=
      angularInverseLift A (x-![d,0,0]) := by
    ext i
    fin_cases i <;> simp [angularRealTranslation,undoAngularPoint]
  rw [he,angularNormalizedLift_inverse hA]

lemma AngularPeriodic.undoAngularPoint {F : Type*} {T : ℝ} {f : Coord3 → F}
    (hf : AngularPeriodic T f) (A : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ) (d : ℝ) :
    AngularPeriodic T (f ∘ undoAngularPoint A θ d) := by
  intro n x
  simp only [Function.comp_apply,ScalarConductivity.undoAngularPoint]
  rw [show x+angularShift T n-![d,0,0]=(x-![d,0,0])+angularShift T n by abel,
    angularInverseLift_shift]
  rw [show ScalarConductivity.angularInverseLift A (x-![d,0,0])+
    angularShift T ![A 1 1*n 0-A 0 1*n 1,-A 1 0*n 0+A 0 0*n 1]-![0,θ 0,θ 1]=
    (ScalarConductivity.angularInverseLift A (x-![d,0,0])-![0,θ 0,θ 1])+
    angularShift T ![A 1 1*n 0-A 0 1*n 1,-A 1 0*n 0+A 0 0*n 1] by abel]
  exact hf _ _

lemma undoAngularValue_matching {s : Fin 3 → ℝ} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : A.det=1) (θ : Fin 2 → ℝ) (d : ℝ) (h₀ : Fin 2 → ℤ)
    (a b pa pb : (Fin 2 → ℤ) → ℝ) {v : Coord3 → Fin 2 → ℝ}
    (hv : ∀ y,y 0∈Icc 0 (1/2) → v y=
      ![y 0+flatFourier s (normalizedFourierCoefficients s 0 d a) pa
        (angularNormalizedLift A (angularRealTranslation θ y))/sqrt (angularNormalization A),
        flatPhaseMode s h₀ (pb h₀) (angularNormalizedLift A (angularRealTranslation θ y))+
        flatFourier s (normalizedFourierCoefficients s (torusRate s h₀) d b) pb
          (angularNormalizedLift A (angularRealTranslation θ y))])
    {x : Coord3} (hx : (x 0-d)/sqrt (angularNormalization A)∈Icc 0 (1/2)) :
    undoAngularValue A θ d (torusRate s h₀) v x=
      ![x 0+flatFourier s a pa x,flatPhaseMode s h₀ (pb h₀) x+flatFourier s b pb x] := by
  have hm : sqrt (angularNormalization A)≠0 := (sqrt_pos.mpr (angularNormalization_pos A)).ne'
  have hxy : (x-![d,0,0])+![d,0,0]=x := sub_add_cancel _ _
  have he : exp (-torusRate s h₀*d)*exp (torusRate s h₀*d)=1 := by
    rw [←exp_add,show -torusRate s h₀*d+torusRate s h₀*d=0 by ring,exp_zero]
  have hmode := flatPhaseMode_translation s h₀ (pb h₀) d (x-![d,0,0])
  rw [hxy] at hmode
  unfold undoAngularValue
  rw [hv _ (by simpa only [undoAngularPoint_zero] using hx),undoAngularPoint_forward hA,
    flatFourier_normalized_translation,flatFourier_normalized_translation,hxy]
  ext j
  fin_cases j
  · change sqrt (angularNormalization A)*(undoAngularPoint A θ d x 0+
      exp (0*d)*flatFourier s a pa x/sqrt (angularNormalization A))+d=x 0+flatFourier s a pa x
    rw [undoAngularPoint_zero]
    simp only [zero_mul,exp_zero,one_mul]
    field_simp [hm]
    ring
  · change exp (-torusRate s h₀*d)*(flatPhaseMode s h₀ (pb h₀) (x-![d,0,0])+
      exp (torusRate s h₀*d)*flatFourier s b pb x)=_
    rw [mul_add,←mul_assoc,he,one_mul,←hmode]
    rfl

lemma undoAngularTensor_matching {s : Fin 3 → ℝ} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : A.det=1) (θ : Fin 2 → ℝ) (d : ℝ) {E : Coord3 → Mat3}
    (hE : ∀ y,y 0∈Icc 0 (1/2) → E y=flatBackgroundTensor (normalizedAngularTensor s A))
    {x : Coord3} (hx : (x 0-d)/sqrt (angularNormalization A)∈Icc 0 (1/2)) :
    undoAngularTensor A θ d E x=flatBackgroundTensor s := by
  rw [undoAngularTensor,hE _ (by simpa only [undoAngularPoint_zero] using hx),
    angularLiftMatrix_background hA,smul_smul,inv_mul_cancel₀ (angularNormalization_pos A).ne',one_smul]

lemma undoAngularValue_terminal (A : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ)
    (d lam T : ℝ) {v : Coord3 → Fin 2 → ℝ} (hv : ∀ y,T≤y 0 → v y=![y 0,0])
    {x : Coord3} (hx : d+sqrt (angularNormalization A)*T≤x 0) :
    undoAngularValue A θ d lam v x=![x 0,0] := by
  have hm : 0 < sqrt (angularNormalization A) := sqrt_pos.mpr (angularNormalization_pos A)
  have hy : T≤undoAngularPoint A θ d x 0 := by
    rw [undoAngularPoint_zero,le_div_iff₀ hm]
    nlinarith
  unfold undoAngularValue
  rw [hv _ hy]
  ext j
  fin_cases j
  · change sqrt (angularNormalization A)*undoAngularPoint A θ d x 0+d=x 0
    rw [undoAngularPoint_zero]
    field_simp [hm.ne']
    ring
  · simp

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_UndoAngularWeakPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real
open scoped Matrix.Norms.Elementwise

namespace WeakFiniteTensorPair

lemma undoAngular_v {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (θ : Fin 2 → ℝ) (d lam : ℝ) (w : WeakFiniteTensorPair {y : Coord3 | 0<y 0}) :
    (w.undoAngular hA θ d lam).v=undoAngularValue A θ d lam w.v := by
  funext x
  change undoAngularOutput A d lam (w.v ((angularNormalizedEquiv A hA).symm
    (x-undoAngularTranslation A θ d)))+![d,0]=_
  rw [undoAngularPoint_eq_affine hA]
  ext i
  fin_cases i <;> simp [undoAngularValue]

lemma undoAngular_E {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (θ : Fin 2 → ℝ) (d lam : ℝ) (w : WeakFiniteTensorPair {y : Coord3 | 0<y 0}) :
    (w.undoAngular hA θ d lam).E=undoAngularTensor A θ d w.E := by
  funext x
  change (angularNormalization A)⁻¹ •
    linearTensorPullback (angularNormalizedEquiv A hA).symm w.E (x-undoAngularTranslation A θ d)=_
  rw [linearTensorPullback,ContinuousLinearEquiv.symm_symm,
    operatorMatrix_angularNormalizedEquiv,undoAngularPoint_eq_affine hA]
  rfl

end WeakFiniteTensorPair
end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real
open scoped Matrix.Norms.Elementwise

theorem general_mode_weak_finite_ending {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {h₀ : Fin 2 → ℤ} (hh₀ : h₀≠0)
    {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s h₀+gb≤torusRate s h)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ),Q.det=1 ∧
      ∃ p T : ℝ,p∈Ioc 0 (1/2) ∧ p<δ ∧ 7<T ∧
      ∃ w : WeakFiniteTensorPair {y : Coord3 | 0<y 0},
        AngularPeriodic (2*Real.pi) w.v ∧ AngularPeriodic (2*Real.pi) w.E ∧
        (∀ x,x 0∈Icc 0 (1/2) → w.v x=
          ![x 0+flatFourier s (normalizedFourierCoefficients s 0
              (sqrt (angularNormalization Q)*(10+1/p)) a) pa
              (angularNormalizedLift Q (angularRealTranslation θ x))/sqrt (angularNormalization Q),
            flatPhaseMode s h₀ (pb h₀) (angularNormalizedLift Q (angularRealTranslation θ x))+
              flatFourier s (normalizedFourierCoefficients s (torusRate s h₀)
                (sqrt (angularNormalization Q)*(10+1/p)) b) pb
                (angularNormalizedLift Q (angularRealTranslation θ x))]) ∧
        (∀ x,x 0∈Icc 0 (1/2) → w.E x=flatBackgroundTensor (normalizedAngularTensor s Q)) ∧
        (∀ x,T≤x 0 → w.v x=![x 0,0]) ∧
        (∀ x,7≤x 0 → w.E x*ᵥPi.single 0 1=Pi.single 0 1) := by
  obtain ⟨Q,θ,k,hQ,_hk,_he,p,T,c,C,hp,hpδ,hT,hc,hcC,
    v,E,hsym,hv,hEm,hvp,hEp,hbound,hvin,hEin,hterm,hnormal,hreg,⟨G,hGc,hG⟩,hpde⟩ :=
    general_mode_finite_ending_raw_normal hs hh₀ hA hB ha hb hga hgb hra hrb hδ
  let w : WeakFiniteTensorPair {y : Coord3 | 0<y 0} := {
    v := v, E := E, symm := hsym, smooth := hv, measurable := hEm,
    elliptic := ⟨c,C,hc,hcC,hbound⟩, regular := hreg,
    G := G, flux_C1 := hGc, constitution := hG,
    weak := by
      intro j ψ hψ hψs
      calc
        (∫ x,fderiv ℝ ψ.val x ((G x).col j))=
            ∫ x,∑ i,(E x*gradientColumns (fderiv ℝ v x)).col j i*
              (smoothDirection (Pi.single i 1) ψ).val x := by
          apply integral_congr_ae
          filter_upwards [hG] with x hx
          rw [coordinate_flux_pairing (fun y => (G y).col j) ψ x,hx]
        _ = 0 := (hpde j ψ hψ hψs).2 }
  exact ⟨Q,θ,hQ,p,T,hp,hpδ,hT,w,hvp,hEp,hvin,hEin,hterm,hnormal⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_UndoAngularProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real
open scoped Matrix.Norms.Elementwise

lemma undoAngularValue_periodic {F : Coord3 → Fin 2 → ℝ} {P : ℝ}
    (hF : AngularPeriodic P F) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (θ : Fin 2 → ℝ) (d lam : ℝ) : AngularPeriodic P (undoAngularValue A θ d lam F) := by
  have h := hF.undoAngularPoint A θ d
  intro n x
  unfold undoAngularValue
  rw [show F (undoAngularPoint A θ d (x+angularShift P n))=F (undoAngularPoint A θ d x) from h n x]

lemma undoAngularTensor_periodic {E : Coord3 → Mat3} {P : ℝ}
    (hE : AngularPeriodic P E) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (θ : Fin 2 → ℝ) (d : ℝ) : AngularPeriodic P (undoAngularTensor A θ d E) := by
  have h := hE.undoAngularPoint A θ d
  intro n x
  unfold undoAngularTensor
  rw [show E (undoAngularPoint A θ d (x+angularShift P n))=E (undoAngularPoint A θ d x) from h n x]

lemma angularLiftMatrix_normal (A : Matrix (Fin 2) (Fin 2) ℤ) :
    angularLiftMatrix A*ᵥPi.single 0 1=sqrt (angularNormalization A) • Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,
    angularLiftMatrix,Pi.single_apply]

lemma angularLiftMatrix_transpose_normal (A : Matrix (Fin 2) (Fin 2) ℤ) :
    (angularLiftMatrix A)ᵀ*ᵥPi.single 0 1=sqrt (angularNormalization A) • Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,
    angularLiftMatrix,Pi.single_apply]

lemma undoAngularTensor_normal {A : Matrix (Fin 2) (Fin 2) ℤ}
    (θ : Fin 2 → ℝ) (d : ℝ) {E : Coord3 → Mat3} {x : Coord3}
    (hE : E (undoAngularPoint A θ d x)*ᵥPi.single 0 1=Pi.single 0 1) :
    undoAngularTensor A θ d E x*ᵥPi.single 0 1=Pi.single 0 1 := by
  rw [undoAngularTensor,Matrix.smul_mulVec,←Matrix.mulVec_mulVec,
    angularLiftMatrix_transpose_normal,←Matrix.mulVec_mulVec,Matrix.mulVec_smul,hE,
    Matrix.mulVec_smul,angularLiftMatrix_normal,smul_smul,smul_smul]
  rw [mul_assoc,←sq,sq_sqrt (angularNormalization_pos A).le,
    inv_mul_cancel₀ (angularNormalization_pos A).ne',one_smul]

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real
open scoped Matrix.Norms.Elementwise

theorem original_mode_finite_ending {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {h₀ : Fin 2 → ℤ} (hh₀ : h₀≠0)
    {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s h₀+gb≤torusRate s h) :
    ∃ d e R : ℝ,0<d ∧ 0<e ∧ d+e<R ∧
      ∃ w : WeakFiniteTensorPair {x : Coord3 | d<x 0},
        AngularPeriodic (2*Real.pi) w.v ∧ AngularPeriodic (2*Real.pi) w.E ∧
        (∀ x,x 0∈Icc d (d+e) → w.v x=
          ![x 0+flatFourier s a pa x,flatPhaseMode s h₀ (pb h₀) x+flatFourier s b pb x]) ∧
        (∀ x,x 0∈Icc d (d+e) → w.E x=flatBackgroundTensor s) ∧
        (∀ x,R≤x 0 → w.v x=![x 0,0]) ∧
        (∀ x,R≤x 0 → w.E x*ᵥPi.single 0 1=Pi.single 0 1) := by
  obtain ⟨Q,θ,hQ,p,T,hp,_hpδ,hT,z,hzp,hEp,hzin,hEin,hzt,hEn⟩ :=
    general_mode_weak_finite_ending (pa:=pa) (pb:=pb) hs hh₀ hA hB ha hb hga hgb hra hrb (by norm_num : (0:ℝ)<1)
  let m := sqrt (angularNormalization Q)
  have hm : 0 < m := sqrt_pos.mpr (angularNormalization_pos Q)
  let d := m*(10+1/p)
  let e := m/2
  let R := d+m*T
  let w := z.undoAngular hQ θ d (torusRate s h₀)
  have hd : 0<d := mul_pos hm (by linarith [one_div_pos.mpr hp.1])
  have he : 0<e := div_pos hm (by norm_num)
  have hdeR : d+e<R := by dsimp [R,e]; nlinarith
  have hxy (x : Coord3) (hx : x 0∈Icc d (d+e)) :
      (x 0-d)/sqrt (angularNormalization Q)∈Icc 0 (1/2) := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hm.le
    · apply (div_le_iff₀ hm).mpr
      dsimp [e] at hx
      linarith [hx.2]
  refine ⟨d,e,R,hd,he,hdeR,w,?_,?_,?_,?_,?_,?_⟩
  · rw [WeakFiniteTensorPair.undoAngular_v]
    exact undoAngularValue_periodic hzp Q θ d _
  · rw [WeakFiniteTensorPair.undoAngular_E]
    exact undoAngularTensor_periodic hEp Q θ d
  · intro x hx
    rw [WeakFiniteTensorPair.undoAngular_v]
    exact undoAngularValue_matching hQ θ d h₀ a b pa pb hzin (hxy x hx)
  · intro x hx
    rw [WeakFiniteTensorPair.undoAngular_E]
    exact undoAngularTensor_matching hQ θ d hEin (hxy x hx)
  · intro x hx
    rw [WeakFiniteTensorPair.undoAngular_v]
    exact undoAngularValue_terminal Q θ d _ T hzt hx
  · intro x hx
    rw [WeakFiniteTensorPair.undoAngular_E]
    apply undoAngularTensor_normal
    apply hEn
    rw [undoAngularPoint_zero]
    apply (le_div_iff₀ hm).mpr
    dsimp [R] at hx
    nlinarith

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusLeadingDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Real

lemma flatFourier_remove_mode {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B)
    (h₀ : Fin 2 → ℤ) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    flatFourier s a phase x=a h₀*flatPhaseMode s h₀ (phase h₀) x+
      flatFourier s (fun h => if h=h₀ then 0 else a h) phase x := by
  classical
  rw [flatFourier,(flatFourier_summable hs ha hx).tsum_eq_add_tsum_ite h₀]
  congr 1
  unfold flatFourier
  apply tsum_congr
  intro h
  split_ifs <;> simp_all

lemma torusRealContinuation_constant_of_no_modes {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : TorusL2) (hf : ∀ h : Fin 2 → ℤ,h≠0 → realTorusCoeff f h=0)
    {x : Fin 3 → ℝ} (hx : 0<x 0) :
    torusRealContinuation s f x=(mFourierCoeff f 0).re := by
  rw [torusRealContinuation_mean_free hs f hx]
  have ha : realTorusAmplitude f=0 := by
    ext h
    simp only [realTorusAmplitude,Pi.zero_apply]
    split_ifs with hh
    · rfl
    · rw [hf h hh,norm_zero]
  simp [ha,flatFourier]

theorem torusRealContinuation_leading_decomposition {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hres : ∀ h l : Fin 2 → ℤ,torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h)
    (f : TorusL2) (hf : ∃ h : Fin 2 → ℤ,h≠0 ∧ realTorusCoeff f h≠0) :
    ∃ (h₀ : Fin 2 → ℤ) (L B g : ℝ) (b : (Fin 2 → ℤ) → ℝ),
      h₀≠0 ∧ 0<L ∧ 0≤B ∧ 0<g ∧
      (∀ h,|b h|≤B) ∧
      (∀ h,b h≠0 → torusRate s h₀+g≤torusRate s h) ∧
      ∀ x : Fin 3 → ℝ,0<x 0 →
        torusRealContinuation s f x=(mFourierCoeff f 0).re+
          L*(flatPhaseMode s h₀ (realTorusPhase f h₀) x+
            flatFourier s b (realTorusPhase f) x) := by
  classical
  let M : Set (Fin 2 → ℤ) := {h | h≠0 ∧ realTorusCoeff f h≠0}
  obtain ⟨h₀,hh₀,_,g,hg,hgap⟩ := torus_leading_rate_gap hs hres hf
    (show 0∉M by simp [M])
  change h₀≠0 ∧ realTorusCoeff f h₀≠0 at hh₀
  have hneg : -h₀≠0 := neg_ne_zero.mpr hh₀.1
  have hn : -h₀≠h₀ := by
    intro he
    apply hh₀.1
    ext i
    have hi := congrFun he i
    change -(h₀ i)=h₀ i at hi
    change h₀ i=0
    omega
  let L := 2*‖realTorusCoeff f h₀‖
  have hL : 0<L := mul_pos (by norm_num) (norm_pos_iff.mpr hh₀.2)
  let a' : (Fin 2 → ℤ) → ℝ := fun h => if h=h₀ then 0 else realTorusAmplitude f h
  let a'' : (Fin 2 → ℤ) → ℝ := fun h => if h= -h₀ then 0 else a' h
  let b : (Fin 2 → ℤ) → ℝ := fun h => a'' h/L
  have ha' (h) : |a' h|≤‖f‖ := by
    dsimp [a']; split_ifs
    · simp
    · exact realTorusAmplitude_bound f h
  have ha'' (h) : |a'' h|≤‖f‖ := by
    dsimp [a'']; split_ifs
    · simp
    · exact ha' h
  refine ⟨h₀,L,‖f‖/L,g,b,hh₀.1,hL,div_nonneg (norm_nonneg _) hL.le,hg,?_,?_,?_⟩
  · intro h
    dsimp [b]
    rw [abs_div,abs_of_pos hL]
    exact (div_le_div_iff_of_pos_right hL).mpr (ha'' h)
  · intro h hh
    have hz : h≠0 := by
      intro he
      apply hh
      simp [b,a'',a',realTorusAmplitude,he]
    have hd : realTorusCoeff f h≠0 := by
      intro he
      apply hh
      simp [b,a'',a',realTorusAmplitude,he]
    have he : h≠h₀ := by
      intro he
      apply hh
      simp [b,a'',a',he]
    have hn' : h≠-h₀ := by
      intro he
      apply hh
      simp [b,a'',he]
    exact hgap h ⟨hz,hd⟩ he hn'
  · intro x hx
    rw [torusRealContinuation_mean_free hs f hx,
      flatFourier_remove_mode hs (realTorusAmplitude_bound f) h₀ hx]
    change (mFourierCoeff f 0).re+(_+flatFourier s a' (realTorusPhase f) x)=_
    rw [flatFourier_remove_mode hs ha' (-h₀) hx]
    have he : realTorusAmplitude f h₀*flatPhaseMode s h₀ (realTorusPhase f h₀) x=
        ‖realTorusCoeff f h₀‖*flatPhaseMode s h₀ (realTorusPhase f h₀) x := by
      simp [realTorusAmplitude,hh₀.1]
    have hen : a' (-h₀)*flatPhaseMode s (-h₀) (realTorusPhase f (-h₀)) x=
        ‖realTorusCoeff f h₀‖*flatPhaseMode s h₀ (realTorusPhase f h₀) x := by
      simpa [a',hn,realTorusAmplitude,hneg,realTorusPhase] using realTorusCoeff_polar_neg s f h₀ x
    rw [he,hen]
    change _=(mFourierCoeff f 0).re+L*(_+flatFourier s (fun h => a'' h/L) _ x)
    rw [flatFourier_div_coefficients]
    rw [mul_add,mul_div_cancel₀ _ hL.ne']
    dsimp [L,a'']
    ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_RankProjectionFirst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma linearTensorPullback_refl (E : Coord3 → Mat3) :
    linearTensorPullback (ContinuousLinearEquiv.refl ℝ Coord3) E=E := by
  funext x
  change operatorMatrix (ContinuousLinearMap.id ℝ Coord3)*E x*
    (operatorMatrix (ContinuousLinearMap.id ℝ Coord3))ᵀ=E x
  rw [operatorMatrix_id,Matrix.one_mul,Matrix.transpose_one,Matrix.mul_one]

namespace WeakFiniteTensorPair

@[simp] lemma output_E {U : Set Coord3} (w : WeakFiniteTensorPair U)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (b : Fin 2 → ℝ) :
    (w.output Q b).E=w.E := by
  funext x
  change linearTensorPullback (ContinuousLinearEquiv.refl ℝ Coord3) w.E (x-0)=_
  rw [linearTensorPullback_refl,sub_zero]

end WeakFiniteTensorPair

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusTraceFiniteEnd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

theorem torus_trace_finite_ending {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hres : ∀ h l : Fin 2 → ℤ,torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h)
    (f g : TorusL2) :
    ∃ d e R : ℝ,0<d ∧ 0<e ∧ d+e<R ∧
      ∃ w : WeakFiniteTensorPair {x : Coord3 | d<x 0},
        AngularPeriodic (2*Real.pi) w.v ∧ AngularPeriodic (2*Real.pi) w.E ∧
        (∀ x,x 0∈Icc d (d+e) → w.v x=
          ![x 0+torusRealContinuation s f x,torusRealContinuation s g x]) ∧
        (∀ x,x 0∈Icc d (d+e) → w.E x=flatBackgroundTensor s) ∧
        (∀ x,R≤x 0 → w.v x=![x 0+(mFourierCoeff f 0).re,(mFourierCoeff g 0).re]) ∧
        (∀ x,R≤x 0 → w.E x*ᵥPi.single 0 1=Pi.single 0 1) := by
  classical
  obtain ⟨ga,hga,hra⟩ := torusRate_uniform_positive hs
  have haf (h : Fin 2 → ℤ) (hh : realTorusAmplitude f h≠0) : ga≤torusRate s h := by
    apply hra h
    intro he
    apply hh
    simp [realTorusAmplitude,he]
  by_cases hg : ∃ h : Fin 2 → ℤ,h≠0 ∧ realTorusCoeff g h≠0
  · obtain ⟨h₀,L,B,gb,b,hh₀,hL,hB,hgb,hb,hrb,heq⟩ :=
      torusRealContinuation_leading_decomposition hs hres g hg
    obtain ⟨d,e,R,hd,he,hdR,w,hvp,hEp,hvi,hEi,hvt,hEt⟩ :=
      original_mode_finite_ending (pa:=realTorusPhase f) (pb:=realTorusPhase g)
        hs hh₀ (norm_nonneg f) hB (realTorusAmplitude_bound f) hb hga hgb haf hrb
    let Q := scaleSecondEquiv L hL.ne'
    let c : Fin 2 → ℝ := ![(mFourierCoeff f 0).re,(mFourierCoeff g 0).re]
    let z := w.output Q c
    refine ⟨d,e,R,hd,he,hdR,z,?_,?_,?_,?_,?_,?_⟩
    · intro n x
      simp only [z,WeakFiniteTensorPair.output_v,hvp n x]
    · simpa only [z,WeakFiniteTensorPair.output_E] using hEp
    · intro x hx
      simp only [z,WeakFiniteTensorPair.output_v,hvi x hx]
      rw [torusRealContinuation_mean_free hs f (hd.trans_le hx.1),heq x (hd.trans_le hx.1)]
      ext i
      fin_cases i <;> simp [Q,c] <;> ring
    · simpa only [z,WeakFiniteTensorPair.output_E] using hEi
    · intro x hx
      simp only [z,WeakFiniteTensorPair.output_v,hvt x hx]
      ext i
      fin_cases i <;> simp [Q,c]
    · simpa only [z,WeakFiniteTensorPair.output_E] using hEt
  · have hgc (h : Fin 2 → ℤ) (hh : h≠0) : realTorusCoeff g h=0 := by
      by_contra hn
      exact hg ⟨h,hh,hn⟩
    have hh₀ : (![1,0] : Fin 2 → ℤ)≠0 := by
      intro hn
      have := congrFun hn 0
      norm_num at this
    obtain ⟨d,e,R,hd,he,hdR,w,hvp,hEp,hvi,hEi,hvt,hEt⟩ :=
      original_mode_finite_ending (pa:=realTorusPhase f) (pb:=fun _ => 0)
        (a:=realTorusAmplitude f) (b:=fun _ => 0) (B:=0) (gb:=1)
        hs hh₀ (norm_nonneg f) le_rfl (realTorusAmplitude_bound f) (by simp)
          hga (by norm_num) haf (by simp)
    let c : Fin 2 → ℝ := ![(mFourierCoeff f 0).re,(mFourierCoeff g 0).re]
    let z := w.projectFirst.output (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) c
    have hzv (x : Coord3) : z.v x=![w.v x 0,0]+c := by
      rw [show z.v x= _ from WeakFiniteTensorPair.output_v _ _ _ x]
      rfl
    have hzE : z.E=w.E := by
      rw [show z.E= _ from WeakFiniteTensorPair.output_E _ _ _]
      rfl
    refine ⟨d,e,R,hd,he,hdR,z,?_,?_,?_,?_,?_,?_⟩
    · intro n x
      rw [hzv,hzv,hvp n x]
    · simpa only [hzE] using hEp
    · intro x hx
      rw [hzv,hvi x hx,torusRealContinuation_mean_free hs f (hd.trans_le hx.1),
        torusRealContinuation_constant_of_no_modes hs g hgc (hd.trans_le hx.1)]
      ext i
      fin_cases i <;> simp [c]
      ring
    · simpa only [hzE] using hEi
    · intro x hx
      rw [hzv,hvt x hx]
      ext i
      fin_cases i <;> simp [c]
    · simpa only [hzE] using hEt

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_TorusEndingCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

theorem torusEndingData_nonempty {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hres : ∀ h l : Fin 2 → ℤ,torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h)
    (f : Fin 2 → TorusL2) : Nonempty (TorusEndingData s f) := by
  obtain ⟨d,e,R,hd,he,hR,w,hpv,hpE,hvi,hEi,hvt,hEt⟩ := torus_trace_finite_ending hs hres (f 0) (f 1)
  exact ⟨⟨d,e,R,hd,he,hR,w,hpv,hpE,hvi,hEi,hvt,hEt⟩⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalFiniteEndingData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma physicalFiniteEndingData_nonempty_oai {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hres : ∀ h l : Fin 2 → ℤ,torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h) :
    Nonempty (PhysicalFiniteEndingData s) := by
  obtain ⟨p,hm,hv,hw,_⟩ := central_pair_regular_exists s
  have he (i : Fin 3) := torusEndingData_nonempty hs hres
    (branchNormalize i (fun j => torusSpectralSynthesis s (centralT s i (p j))))
  exact ⟨⟨p,hm,hv,hw,fun i => Classical.choice (he i)⟩⟩

end ScalarConductivity

end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.physicalFiniteEndingData_nonempty_oai := @OAI.ScalarConductivity.physicalFiniteEndingData_nonempty_oai
