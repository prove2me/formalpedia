-- Prove2me | solution 1 for OAI.ScalarConductivity.matchedEnding_weak_equation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:19:08.043025+00:00
-- url     : https://prove2.me/submissions/f402a758-47e3-4d15-acfe-0ba6c142abd9

import Mathlib
import Definitions.Def_OAIQ059C007
import Theorems.Thm_OAI_ScalarConductivity_endingJoin_constitution_ae

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
lemma connectorRate_right {K z : ℝ} (hK : 0 < K) (hz : K+1 ≤ z) :
    connectorRate K z = 3 := by
  rw [connectorRate,smoothTransition.one_of_one_le
    ((le_div_iff₀ hK).mpr (by linarith))]
  ring

lemma connectorProfile_pos (K z : ℝ) : 0 < connectorProfile K z := exp_pos _
lemma connectorProfile_smooth (K : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (connectorProfile K) := by
  let r : SmoothScalar ℝ := ⟨connectorRate K,connectorRate_smooth K⟩
  exact ((smoothScalar_contDiff (smoothPrimitive r)).neg).exp

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

lemma connectorProfile_right {K z : ℝ} (hK : 0 < K) (hz : K+1 ≤ z) :
    connectorProfile K z = connectorProfile K (K+2)*exp (-3*(z-(K+2))) := by
  have hi : (∫ t in (K+2)..z, connectorRate K t) = 3*(z-(K+2)) := by
    calc
      _ = ∫ _t in (K+2)..z, (3:ℝ) := intervalIntegral.integral_congr (by
        intro t ht
        apply connectorRate_right hK
        exact le_trans (le_min (by linarith) hz) ht.1)
      _ = _ := by simp; ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((connectorRate_smooth K).continuous.intervalIntegrable 0 (K+2))
    ((connectorRate_smooth K).continuous.intervalIntegrable (K+2) z)
  rw [hi] at hadd
  unfold connectorProfile
  rw [←hadd,neg_add,exp_add]
  congr 2
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

lemma cascadeProfile_connector {L K t : ℝ} (hL : 0 < L) (ht₁ : 0 ≤ t) (ht₂ : t ≤ K+2) :
    cascadeProfile L K t = connectorProfile K t := by
  rw [cascadeProfile,crossingOn_eq_one hL (show -L/2 ≤ t/2+L by linarith),
    crossingOff_eq_one hL (show t-(K+2+L) ≤ L/2 by linarith)]
  ring

lemma cascadeProfile_incoming {L K t : ℝ} (hL : 0 < L) (hK : 0 < K) (ht : t ≤ 0) :
    cascadeProfile L K t = crossingOn L (t/2+L)*exp (-t/2) := by
  rw [cascadeProfile,connectorProfile_left hK (show t≤1 by linarith),
    crossingOff_eq_one hL (show t-(K+2+L) ≤ L/2 by linarith),mul_one]

lemma cascadeProfile_outgoing {L K t : ℝ} (hL : 0 < L) (hK : 0 < K) (ht : K+2 ≤ t) :
    cascadeProfile L K t = connectorProfile K (K+2)*exp (-3*(t-(K+2))) *
      crossingOff L (t-(K+2+L)) := by
  rw [cascadeProfile,crossingOn_eq_one hL (show -L/2≤t/2+L by linarith),one_mul,
    connectorProfile_right hK (show K+1≤t by linarith)]

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

lemma cascadePhase_before {D k t : ℝ} (hD : 0 < D) {i j : ℕ}
    (hij : i < j) (hj : 0 ≤ cascadePhase D k j t) :
    D ≤ cascadePhase D k i t := by
  by_cases ht : k*t ≤ 2*D
  · have h := cascadePhase_antitone ht (show i+1≤j by omega)
    dsimp only at h
    rw [cascadePhase_succ] at h
    linarith
  · have hp : 0 ≤ (2:ℝ)^i := by positivity
    have : 0 ≤ (2:ℝ)^i*(k*t-2*D) := mul_nonneg hp (by linarith)
    unfold cascadePhase
    linarith

lemma cascadePhase_after {D k t : ℝ} (hD : 0 < D) {i j : ℕ}
    (hij : j+1 < i) (hj : cascadePhase D k j t ≤ D) :
    cascadePhase D k i t ≤ -2*D := by
  have ht : k*t ≤ 2*D := by
    by_contra hh
    have hp : 0 < (2:ℝ)^j := by positivity
    have : 0 < (2:ℝ)^j*(k*t-2*D) := mul_pos hp (by linarith)
    unfold cascadePhase at hj
    linarith
  have h := cascadePhase_antitone ht (show j + 2 ≤ i by omega)
  dsimp only at h
  rw [show j+2=(j+1)+1 by omega,cascadePhase_succ,cascadePhase_succ] at h
  linarith

lemma cascadeProfile_only_two {L K k t : ℝ} (hL : 0 < L) (hK : 0 < K)
    {j i : ℕ} (hj₁ : 0 ≤ cascadePhase (cascadeLength L K) k j t)
    (hj₂ : cascadePhase (cascadeLength L K) k j t ≤ cascadeLength L K)
    (hi : i ≠ j) (hi' : i ≠ j+1) :
    cascadeProfile L K (cascadePhase (cascadeLength L K) k i t) = 0 := by
  have hD := cascade_length_positive hL hK
  by_cases hij : i < j
  · apply cascadeProfile_zero_right hL
    have hh := cascadePhase_before hD hij hj₁
    change K+2+2*L ≤ cascadePhase (cascadeLength L K) k i t at hh
    linarith
  · apply cascadeProfile_zero_left hL
    have hh := cascadePhase_after hD (show j+1 < i by omega) hj₂
    change cascadePhase (cascadeLength L K) k i t ≤ -2*(K+2+2*L) at hh
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

lemma cascadeValue_two_modes {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (A : ℝ)
    (x : Coord3) (j : ℕ) (hj₁ : 0 ≤ cascadePhase (cascadeLength L K) k j (x 0))
    (hj₂ : cascadePhase (cascadeLength L K) k j (x 0) ≤ cascadeLength L K) :
    cascadeValue L K k A x = cascadeTerm L K k A j x + cascadeTerm L K k A (j+1) x := by
  have h : (∑' i : ℕ, cascadeTerm L K k A i x) = ∑ i ∈ ({j,j+1} : Finset ℕ), cascadeTerm L K k A i x := tsum_eq_sum (s := ({j,j+1} : Finset ℕ)) (f := fun i => cascadeTerm L K k A i x) (by
    intro i hi
    have hi₁ : i ≠ j := by simpa using fun h => hi (by simp [h])
    have hi₂ : i ≠ j+1 := by simpa using fun h => hi (by simp [h])
    rw [cascadeTerm,cascadeProfile_only_two hL hK hj₁ hj₂ hi₁ hi₂,mul_zero,zero_mul])
  simpa [cascadeValue,Finset.sum_pair (show j ≠ j+1 by omega)] using h

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

lemma direction_commute {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (v w x : E) :
    direction v (direction w f) x = direction w (direction v f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (show (1 : WithTop ℕ∞)+1≤2 by norm_num)).contDiffAt.differentiableAt (by norm_num)
  unfold direction
  rw [fderiv_clm_apply hd (differentiableAt_const _),fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hf.contDiffAt.isSymmSndFDerivAt (by simp) v w

lemma direction_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : Differentiable ℝ f) (v x : E) :
    direction v (fun x => -f x) x = -direction v f x := by
  change (fderiv ℝ (-f) x) v = -(fderiv ℝ f x) v
  rw [(hf x).hasFDerivAt.neg.fderiv]
  rfl

theorem antisymmetric_potential_divergence {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (v : ι → E) (S : ι → ι → E → ℝ)
    (hS : ∀ i j, ContDiff ℝ 2 (S i j))
    (ha : ∀ i j, S i j = fun x => -S j i x) (x : E) :
    ∑ i, direction (v i) (fun y => ∑ j, direction (v j) (S i j) y) x = 0 := by
  have hsum (i : ι) :
      direction (v i) (fun y => ∑ j, direction (v j) (S i j) y) x =
      ∑ j, direction (v i) (direction (v j) (S i j)) x := by
    change (fderiv ℝ (fun y => ∑ j, direction (v j) (S i j) y) x) (v i) = _
    rw [fderiv_fun_sum (fun j _ => (direction_C1 (hS i j) (v j)).contDiffAt.differentiableAt (by norm_num))]
    simp [direction]
  simp_rw [hsum]
  have he (i j : ι) : direction (v i) (direction (v j) (S i j)) x =
      -direction (v j) (direction (v i) (S j i)) x := by
    rw [direction_commute (hS i j),ha i j]
    have hn : direction (v i) (fun x => -S j i x) = fun x => -direction (v i) (S j i) x := by
      funext y
      exact direction_neg ((hS j i).differentiable (by norm_num)) _ _
    rw [hn]
    exact direction_neg ((direction_C1 (hS j i) _).differentiable (by norm_num)) _ _
  have heq : (∑ i, ∑ j, direction (v i) (direction (v j) (S i j)) x) =
      -(∑ i, ∑ j, direction (v i) (direction (v j) (S i j)) x) := by
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => enter [2,i,2,j]; rw [he]
    simp only [Finset.sum_neg_distrib]
  linarith

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

lemma cascadePotentialMother_antisymm (L K : ℝ) (a b i j : Fin 3) :
    cascadePotentialMother L K a b i j = fun x => -cascadePotentialMother L K a b j i x := by
  funext x
  unfold cascadePotentialMother
  ring

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

lemma cascadePotential_antisymm (L K k A : ℝ) (i j : Fin 3) :
    cascadePotential L K k A i j = fun x => -cascadePotential L K k A j i x := by
  funext x
  unfold cascadePotential
  simp_rw [cascadePotentialMother_antisymm L K _ _ i j, mul_neg,tsum_neg]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_C1WeakDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma direction_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (v : E) : Continuous (direction v f) := by
  have hd : ContDiff ℝ 0 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact hd.continuous.clm_apply continuous_const

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

lemma crossing_first_on_left {L z : ℝ} (hL : 0 < L) (hz : z ≤ 0) :
    crossingFirst L z = exp (-3*z) := by
  rw [crossingFirst,crossingOff_eq_one hL (by linarith),one_mul]
lemma crossing_second_on_right {L z : ℝ} (hL : 0 < L) (hz : 0 ≤ z) :
    crossingSecond L z = exp (-z) := by
  rw [crossingSecond,crossingOn_eq_one hL (by linarith),one_mul]

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

lemma crossing_current_constitution {L : ℝ} (hL : 0 < L) (z x y : ℝ) :
    crossingCurrentX L z x y =
      crossingXX L z x y*(-crossingFirst L z*sin x) +
      crossingXY L z x y*(-2*crossingSecond L z*sin (2*y)) ∧
    crossingCurrentY L z x y =
      crossingXY L z x y*(-crossingFirst L z*sin x) +
      crossingYY L z x y*(-2*crossingSecond L z*sin (2*y)) := by
  have he₁ : exp (-3*z) ≠ 0 := (exp_pos _).ne'
  have he₂ : exp (-z) ≠ 0 := (exp_pos _).ne'
  by_cases hz : z ≤ 0
  · have hf := crossing_first_on_left hL hz
    have hr := crossingResidualFirst_zero hL (show z < L/2 by linarith)
    obtain ⟨hyy,hxy⟩ := crossing_corrections_left hL hz x y
    rw [hyy,hxy]
    constructor <;> dsimp only [crossingCurrentX,crossingCurrentY,crossingXX] <;>
      rw [hr,hf] <;> simp only [crossingHxx,crossingHxy,one_mul,one_pow,mul_one] <;>
      field_simp <;> ring
  · have hg := crossing_second_on_right hL (le_of_not_ge hz)
    have hr := crossingResidualSecond_zero hL (show -L/2 < z by linarith)
    obtain ⟨hxx,hxy⟩ := crossing_corrections_right hL (le_of_not_ge hz) x y
    rw [hxx,hxy]
    constructor <;> dsimp only [crossingCurrentX,crossingCurrentY,crossingYY] <;>
      rw [hr,hg] <;> simp only [crossingHxx,crossingHxy,one_mul,mul_one] <;>
      field_simp <;> ring

lemma cascadeProfile_next_connector_zero {L K s : ℝ} (hL : 0 < L)
    (hs : s ≤ K+2) : cascadeProfile L K (2*(s-cascadeLength L K)) = 0 := by
  apply cascadeProfile_zero_left hL
  unfold cascadeLength
  linarith

lemma cascadeProfile_crossing_current {L K s : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hs : K+2 ≤ s) :
    cascadeProfile L K s = connectorProfile K (K+2)*exp (-3*L)*
      crossingFirst L (s-(K+2+L)) := by
  rw [cascadeProfile_outgoing hL hK hs,crossingFirst]
  have he : exp (-3*(s-(K+2))) = exp (-3*L)*exp (-3*(s-(K+2+L))) := by
    rw [←exp_add]
    congr 1
    ring
  rw [he]
  ring

lemma cascadeProfile_crossing_next {L K s : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hs : s ≤ cascadeLength L K) :
    cascadeRatio L K*cascadeProfile L K (2*(s-cascadeLength L K)) =
      connectorProfile K (K+2)*exp (-3*L)*crossingSecond L (s-(K+2+L)) := by
  rw [cascadeProfile_incoming hL hK (by linarith),cascadeRatio,crossingSecond]
  have ha : 2*(s-cascadeLength L K)/2+L = s-(K+2+L) := by
    unfold cascadeLength
    ring
  rw [ha]
  have he : exp (-4*L)*exp (-(2*(s-cascadeLength L K))/2) =
      exp (-3*L)*exp (-(s-(K+2+L))) := by
    rw [←exp_add,←exp_add]
    congr 1
    unfold cascadeLength
    ring
  calc
    _ = connectorProfile K (K+2)*crossingOn L (s-(K+2+L))*
        (exp (-4*L)*exp (-(2*(s-cascadeLength L K))/2)) := by ring
    _ = _ := by rw [he]; ring

lemma cascade_overlap_value {L K s : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hs₁ : K+2 ≤ s) (hs₂ : s ≤ cascadeLength L K) (a x y : ℝ) :
    a*cascadeProfile L K s*cos x +
      (a*cascadeRatio L K)*cascadeProfile L K (2*(s-cascadeLength L K))*cos (2*y) =
    (a*connectorProfile K (K+2)*exp (-3*L))*crossingValue L (s-(K+2+L)) x y := by
  rw [cascadeProfile_crossing_current hL hK hs₁]
  have hh := cascadeProfile_crossing_next hL hK hs₂
  dsimp only [crossingValue]
  calc
    _ = a*(connectorProfile K (K+2)*exp (-3*L)*crossingFirst L (s-(K+2+L)))*cos x +
      a*(cascadeRatio L K*cascadeProfile L K (2*(s-cascadeLength L K)))*cos (2*y) := by ring
    _ = _ := by rw [hh]; ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeProfileDeriv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma cascadeProfile_crossing_current_deriv {L K s : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hs : K+2 < s) :
    deriv (cascadeProfile L K) s = connectorProfile K (K+2)*exp (-3*L)*
      deriv (crossingFirst L) (s-(K+2+L)) := by
  have he : cascadeProfile L K =ᶠ[𝓝 s]
      fun r => connectorProfile K (K+2)*exp (-3*L)*crossingFirst L (r-(K+2+L)) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    exact cascadeProfile_crossing_current hL hK hr.le
  have hd : HasDerivAt (fun r => connectorProfile K (K+2)*exp (-3*L)*crossingFirst L (r-(K+2+L)))
      (connectorProfile K (K+2)*exp (-3*L)*deriv (crossingFirst L) (s-(K+2+L))) s := by
    simpa only [id_eq,mul_one,Function.comp_def] using (((crossingFirst_smooth L).differentiable (by simp) _).hasDerivAt.comp s
      ((hasDerivAt_id s).sub_const (K+2+L))).const_mul (connectorProfile K (K+2)*exp (-3*L))
  rw [he.deriv_eq,hd.deriv]

lemma cascadeProfile_crossing_next_deriv {L K s : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hs : s < cascadeLength L K) :
    cascadeRatio L K*deriv (cascadeProfile L K) (2*(s-cascadeLength L K)) =
      (connectorProfile K (K+2)*exp (-3*L)/2)*deriv (crossingSecond L) (s-(K+2+L)) := by
  have he : (fun r => cascadeRatio L K*cascadeProfile L K (2*(r-cascadeLength L K))) =ᶠ[𝓝 s]
      fun r => connectorProfile K (K+2)*exp (-3*L)*crossingSecond L (r-(K+2+L)) := by
    filter_upwards [Iio_mem_nhds hs] with r hr
    exact cascadeProfile_crossing_next hL hK hr.le
  have hd₁ : HasDerivAt (fun r => cascadeRatio L K*cascadeProfile L K (2*(r-cascadeLength L K)))
      (2*cascadeRatio L K*deriv (cascadeProfile L K) (2*(s-cascadeLength L K))) s := by
    simpa only [id_eq,mul_one,one_mul,Function.comp_def,mul_assoc,mul_left_comm,mul_comm] using (((cascadeProfile_smooth L K).differentiable (by simp) _).hasDerivAt.comp s
      (((hasDerivAt_id s).sub_const (cascadeLength L K)).const_mul 2)).const_mul (cascadeRatio L K)
  have hd₂ : HasDerivAt (fun r => connectorProfile K (K+2)*exp (-3*L)*crossingSecond L (r-(K+2+L)))
      (connectorProfile K (K+2)*exp (-3*L)*deriv (crossingSecond L) (s-(K+2+L))) s := by
    simpa only [id_eq,mul_one,Function.comp_def] using (((crossingSecond_smooth L).differentiable (by simp) _).hasDerivAt.comp s
      ((hasDerivAt_id s).sub_const (K+2+L))).const_mul (connectorProfile K (K+2)*exp (-3*L))
  have hh := he.deriv_eq
  rw [hd₁.deriv,hd₂.deriv] at hh
  linarith

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

lemma cascadePhase_lt_terminal {D k t : ℝ} {j : ℕ}
    (hj : cascadePhase D k j t  <  2*D) : k*t  <  2*D := by
  have hp : 0  <  (2:ℝ)^j := by positivity
  unfold cascadePhase at hj
  nlinarith

lemma cascadePhase_before_wide {D k t : ℝ} {i j : ℕ} (ht : k*t ≤ 2*D) (hij : i < j) :
    D+cascadePhase D k j t/2  ≤  cascadePhase D k i t := by
  have hh := cascadePhase_antitone ht (show i+1 ≤ j by omega)
  dsimp only at hh
  rw [cascadePhase_succ] at hh
  linarith

lemma cascadePhase_after_wide {D k t : ℝ} {i j : ℕ} (ht : k*t ≤ 2*D) (hij : j+1 < i) :
    cascadePhase D k i t  ≤  4*cascadePhase D k j t-6*D := by
  have hh := cascadePhase_antitone ht (show j+2 ≤ i by omega)
  dsimp only at hh
  rw [show j+2=(j+1)+1 by omega,cascadePhase_succ,cascadePhase_succ] at hh
  linarith

lemma cascadePhase_inactive_wide {L K k t : ℝ} (hL : 0  <  L) (hK : 0  <  K) {j i : ℕ}
    (hj₁ : -L/8  <  cascadePhase (cascadeLength L K) k j t)
    (hj₂ : cascadePhase (cascadeLength L K) k j t  <  cascadeLength L K+L/8)
    (hi : i≠j) (hi' : i≠j+1) :
    cascadePhase (cascadeLength L K) k i t  <  -7*L/2 ∨
      K+2+7*L/4  <  cascadePhase (cascadeLength L K) k i t := by
  have ht : k*t < 2*cascadeLength L K := cascadePhase_lt_terminal (hj₂.trans
    (by unfold cascadeLength; linarith))
  by_cases hij : i < j
  · right
    have hh := cascadePhase_before_wide ht.le hij
    unfold cascadeLength at *
    linarith
  · left
    have hh := cascadePhase_after_wide ht.le (show j+1 < i by omega)
    unfold cascadeLength at *
    linarith

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
lemma cascadeCrossStream_zero_right {L K : ℝ} (hL : 0 < L) (a b : Fin 3) (x : Coord3)
    (ht : K+2+7*L/4 < x 0) : cascadeCrossStream L K a b x = 0 := by
  have hf := crossingResidualFirst_zero_right hL (show 3*L/4 < x 0-(K+2+L) by linarith)
  have hg := crossingResidualSecond_zero hL (show -L/2 < x 0-(K+2+L) by linarith)
  simp [cascadeCrossStream,hf,hg]

lemma cascadeMother_inactive_wide {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (hk : k≠0)
    (x : Coord3) {j n : ℕ}
    (hj₁ : -L/8  <  cascadePhase (cascadeLength L K) k j (x 0))
    (hj₂ : cascadePhase (cascadeLength L K) k j (x 0)  <  cascadeLength L K+L/8)
    (hn : n≠j) (hn' : n≠j+1) :
    cascadeMother L K (cascadeAxis n) ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)) = 0 ∧
    cascadeBaseStream L K (cascadeAxis n) ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)) = 0 ∧
    cascadeCrossStream L K (cascadeAxis n) (cascadeAxis (n+1))
      ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)) = 0 := by
  let y := (k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)
  have ht : y 0 <  -7*L/2 ∨ K+2+7*L/4 < y 0 := by
    dsimp only [y]
    rw [cascade_dilation_time hk]
    exact cascadePhase_inactive_wide hL hK hj₁ hj₂ hn hn'
  refine ⟨?_,cascadeBaseStream_zero hL _ y ht,?_⟩
  · have hp : cascadeProfile L K (y 0) = 0 := ht.elim
      (fun h => cascadeProfile_zero_left hL h.le) (fun h => cascadeProfile_zero_right hL h.le)
    exact show cascadeProfile L K (y 0)*cos (y (cascadeAxis n))=0 by rw [hp,zero_mul]
  · rcases ht with ht | ht
    · apply cascadeCrossStream_zero_left hL _ _ y
      linarith
    · exact cascadeCrossStream_zero_right hL _ _ y ht

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CascadeFluxLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma cascadePotentialTerm_inactive {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (hk : k≠0)
    (A : ℝ) (x : Coord3) {m n : ℕ}
    (hm₁ : -L/8 < cascadePhase (cascadeLength L K) k m (x 0))
    (hm₂ : cascadePhase (cascadeLength L K) k m (x 0) < cascadeLength L K+L/8)
    (hn : n≠m) (hn' : n≠m+1) (i j : Fin 3) :
    cascadePotentialTerm L K k A n i j x = 0 := by
  obtain ⟨_,hb,hc⟩ := cascadeMother_inactive_wide hL hK hk x hm₁ hm₂ hn hn'
  simp [cascadePotentialTerm,cascadePotentialMother,hb,hc]

lemma cascadePotential_two_terms {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (hk : k≠0)
    (A : ℝ) (x : Coord3) {m : ℕ}
    (hm₁ : -L/8 < cascadePhase (cascadeLength L K) k m (x 0))
    (hm₂ : cascadePhase (cascadeLength L K) k m (x 0) < cascadeLength L K+L/8)
    (i j : Fin 3) : cascadePotential L K k A i j x =
      cascadePotentialTerm L K k A m i j x + cascadePotentialTerm L K k A (m+1) i j x := by
  have he : (∑' n : ℕ, cascadePotentialTerm L K k A n i j x) =
      ∑ n ∈ ({m,m+1} : Finset ℕ), cascadePotentialTerm L K k A n i j x :=
    tsum_eq_sum (s := ({m,m+1} : Finset ℕ)) (fun n hn =>
      cascadePotentialTerm_inactive hL hK hk A x hm₁ hm₂
        (by simpa using fun h => hn (by simp [h]))
        (by simpa using fun h => hn (by simp [h])) i j)
  simpa [cascadePotential,cascadePotentialTerm,Finset.sum_pair (show m≠m+1 by omega)] using he

lemma cascadePotential_terminal {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (ht : 2*cascadeLength L K ≤ k*x 0) (i j : Fin 3) :
    cascadePotential L K k A i j x = 0 := by
  have hh (n : ℕ) : cascadePotentialTerm L K k A n i j x = 0 := by
    let y := (k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)
    have hy : K+2+7*L/4 < y 0 := by
      dsimp only [y]
      rw [cascade_dilation_time hk,cascadePhase]
      have hp : 0 ≤ (2:ℝ)^n*(k*x 0-2*cascadeLength L K) := mul_nonneg (by positivity) (by linarith)
      unfold cascadeLength at *
      linarith
    have hb := cascadeBaseStream_zero hL (cascadeAxis n) y (Or.inr hy)
    have hc := cascadeCrossStream_zero_right hL (cascadeAxis n) (cascadeAxis (n+1)) y hy
    change (A*cascadeRatio L K^n)*cascadePotentialMother L K (cascadeAxis n) (cascadeAxis (n+1)) i j y=0
    simp [cascadePotentialMother,hb,hc]
  change (∑' n : ℕ, cascadePotentialTerm L K k A n i j x)=0
  simp only [hh,tsum_zero]

lemma cascadeFlux_terminal_strict {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (ht : 2*cascadeLength L K < k*x 0) (i : Fin 3) :
    cascadeFlux L K k A x i = 0 := by
  have hn : {y : Coord3 | 2*cascadeLength L K < k*y 0} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (continuous_const.mul (continuous_apply 0))).mem_nhds ht
  unfold cascadeFlux
  apply Finset.sum_eq_zero
  intro j _
  have he : cascadePotential L K k A i j =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [hn] with y hy
    exact cascadePotential_terminal hL hK hk A y hy.le i j
  simp [direction,he.fderiv_eq]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_DirectionCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

section Direction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}

lemma direction_add {f g : E → ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (v : E) : direction v (fun y => f y+g y) x = direction v f x+direction v g x := by
  simp only [direction,fderiv_fun_add hf hg,add_apply]
lemma direction_sub {f g : E → ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (v : E) : direction v (fun y => f y-g y) x = direction v f x-direction v g x := by
  simp only [direction,fderiv_fun_sub hf hg,sub_apply]
lemma direction_mul {f g : E → ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (v : E) : direction v (fun y => f y*g y) x = f x*direction v g x+g x*direction v f x := by
  simp only [direction,fderiv_fun_mul hf hg,add_apply,
    smul_apply,smul_eq_mul]
lemma direction_const_mul {f : E → ℝ} (hf : DifferentiableAt ℝ f x) (c : ℝ) (v : E) :
    direction v (fun y => c*f y) x = c*direction v f x := by
  rw [direction_mul (differentiableAt_const _) hf,direction_const,mul_zero,add_zero]
lemma direction_comp_real {f : E → ℝ} {g : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) (v : E) :
    direction v (fun y => g (f y)) x = deriv g (f x)*direction v f x := by
  have hh := hg.hasDerivAt.comp_hasFDerivAt x hf.hasFDerivAt
  change (fderiv ℝ (g ∘ f) x) v = deriv g (f x)*direction v f x
  rw [hh.fderiv]
  simp only [smul_apply,smul_eq_mul]
  rfl
lemma direction_congr_nhds {f g : E → ℝ} (h : f =ᶠ[𝓝 x] g) (v : E) :
    direction v f x = direction v g x := by rw [direction,direction,h.fderiv_eq]
end Direction

lemma direction_scalar_coord {f : ℝ → ℝ} (hf : Differentiable ℝ f) (i j : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => f (y j)) x =
      deriv f (x j)*(if j=i then 1 else 0) := by
  rw [direction_comp_real (differentiableAt_pi.1 differentiableAt_id j) (hf _) _,
    direction_coord]

lemma wedgePotential_flux (a b i : Fin 3) {H : Coord3 → ℝ} (hH : Differentiable ℝ H) (x : Coord3) :
    (∑ j, direction (Pi.single j 1) (wedgePotential a b H i j) x) =
      (if i=a then direction (Pi.single b 1) H x else 0) -
      (if i=b then direction (Pi.single a 1) H x else 0) := by
  have hd (i j : Fin 3) : direction (Pi.single j 1) (wedgePotential a b H i j) x =
      (if i=a ∧ j=b then direction (Pi.single j 1) H x else 0) -
      (if j=a ∧ i=b then direction (Pi.single j 1) H x else 0) := by
    unfold wedgePotential
    split <;> split <;>
      simp only [direction_sub (hH x) (hH x),
        direction_sub (differentiableAt_const _) (hH x), direction_const,sub_zero]
  simp_rw [hd]
  rw [Finset.sum_sub_distrib]
  congr 1
  · by_cases h : i=a <;> simp only [h,true_and,false_and,ite_true,ite_false] <;> simp
  · by_cases h : i=b <;> simp only [h,and_true,and_false,ite_true,ite_false] <;> simp

lemma direction_dilation {f : Coord3 → ℝ} (hf : Differentiable ℝ f)
    (s r : ℝ) (c v x : Coord3) :
    direction v (fun y => s*f (r • (y-c))) x = s*r*direction v f (r • (x-c)) := by
  have hl : HasFDerivAt (fun y : Coord3 => r • (y-c)) (r • ContinuousLinearMap.id ℝ Coord3) x :=
    ((hasFDerivAt_id x).sub_const c).const_smul r
  have hh : HasFDerivAt (fun y => s*f (r • (y-c)))
      (s • (fderiv ℝ f (r • (x-c))).comp (r • ContinuousLinearMap.id ℝ Coord3)) x :=
    ((hf _).hasFDerivAt.comp x hl).const_mul s
  change (fderiv ℝ (fun y => s*f (r • (y-c))) x) v = _
  rw [hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul,direction]
  ring

lemma direction_sin_coord (r : ℝ) (i j : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => sin (r*y j)) x =
      r*cos (r*x j)*(if j=i then 1 else 0) := by
  have hh (t : ℝ) : HasDerivAt (fun t => sin (r*t)) (r*cos (r*t)) t := by
    convert ((hasDerivAt_id t).const_mul r).sin using 1 <;> simp [mul_comm]
  rw [direction_scalar_coord (fun t => (hh t).differentiableAt), (hh _).deriv]
lemma direction_cos_coord (r : ℝ) (i j : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => cos (r*y j)) x =
      -r*sin (r*x j)*(if j=i then 1 else 0) := by
  have hh (t : ℝ) : HasDerivAt (fun t => cos (r*t)) (-r*sin (r*t)) t := by
    convert ((hasDerivAt_id t).const_mul r).cos using 1 <;> simp [mul_comm]
  rw [direction_scalar_coord (fun t => (hh t).differentiableAt), (hh _).deriv]

lemma direction_scalar_sin {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (r : ℝ) (i a : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => f (y 0)*sin (r*y a)) x =
      f (x 0)*(r*cos (r*x a)*(if a=i then 1 else 0)) +
      sin (r*x a)*(deriv f (x 0)*(if (0:Fin 3)=i then 1 else 0)) := by
  rw [direction_mul (by fun_prop) (by fun_prop),direction_sin_coord,direction_scalar_coord hf]

lemma angularStream_diff {F G : ℝ → ℝ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (a b : Fin 3) : Differentiable ℝ (angularStream F G a b) := by
  unfold angularStream
  fun_prop

lemma angularStream_b {F G : ℝ → ℝ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    {a b : Fin 3} (hb : b≠0) (hab : a≠b) (x : Coord3) :
    direction (Pi.single b 1) (angularStream F G a b) x =
      F (x 0)*cos (4*x b)*sin (x a) - G (x 0)*cos (x a)*sin (x a)*cos (2*x b) := by
  have zF : direction (Pi.single b 1) (fun y : Coord3 => F (y 0)/4) x = 0 := by
    have he : (fun y : Coord3 => F (y 0)/4) = fun y => (1/4)*F (y 0) := by funext y; ring
    rw [he,direction_const_mul (by fun_prop),direction_scalar_coord hF]
    simp [Ne.symm hb]
  have zG : direction (Pi.single b 1) (fun y : Coord3 => G (y 0)/2) x = 0 := by
    have he : (fun y : Coord3 => G (y 0)/2) = fun y => (1/2)*G (y 0) := by funext y; ring
    rw [he,direction_const_mul (by fun_prop),direction_scalar_coord hG]
    simp [Ne.symm hb]
  have hsin : direction (Pi.single b 1) (fun y : Coord3 => sin (y a)) x = 0 := by
    simpa [hab] using direction_sin_coord 1 b a x
  have hcos : direction (Pi.single b 1) (fun y : Coord3 => cos (y a)) x = 0 := by
    simpa [hab] using direction_cos_coord 1 b a x
  unfold angularStream
  simp (disch := fun_prop) only [direction_sub,direction_mul,zF,zG,hsin,hcos,direction_sin_coord]
  simp only [ite_true,mul_zero,add_zero,zero_add]
  ring

lemma angularStream_a {F G : ℝ → ℝ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    {a b : Fin 3} (ha : a≠0) (hab : a≠b) (x : Coord3) :
    direction (Pi.single a 1) (angularStream F G a b) x =
      F (x 0)/4*sin (4*x b)*cos (x a) -
        G (x 0)/2*((cos (x a))^2-(sin (x a))^2)*sin (2*x b) := by
  have zF : direction (Pi.single a 1) (fun y : Coord3 => F (y 0)/4) x = 0 := by
    have he : (fun y : Coord3 => F (y 0)/4) = fun y => (1/4)*F (y 0) := by funext y; ring
    rw [he,direction_const_mul (by fun_prop),direction_scalar_coord hF]
    simp [Ne.symm ha]
  have zG : direction (Pi.single a 1) (fun y : Coord3 => G (y 0)/2) x = 0 := by
    have he : (fun y : Coord3 => G (y 0)/2) = fun y => (1/2)*G (y 0) := by funext y; ring
    rw [he,direction_const_mul (by fun_prop),direction_scalar_coord hG]
    simp [Ne.symm ha]
  have hsin : direction (Pi.single a 1) (fun y : Coord3 => sin (y a)) x = cos (x a) := by
    simpa using direction_sin_coord 1 a a x
  have hcos : direction (Pi.single a 1) (fun y : Coord3 => cos (y a)) x = -sin (x a) := by
    simpa using direction_cos_coord 1 a a x
  unfold angularStream
  simp (disch := fun_prop) only [direction_sub,direction_mul,zF,zG,hsin,hcos,direction_sin_coord]
  simp only [Ne.symm hab,ite_false,mul_zero,add_zero,zero_add]
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PotentialCurl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma potentialCurl_add {S T : Fin 3 → Fin 3 → Coord3 → ℝ}
    (hS : ∀ i j, Differentiable ℝ (S i j)) (hT : ∀ i j, Differentiable ℝ (T i j)) (x : Coord3) (i : Fin 3) :
    potentialCurl (fun i j x => S i j x+T i j x) x i = potentialCurl S x i+potentialCurl T x i := by
  simp only [potentialCurl,direction_add (hS _ _ _) (hT _ _ _),Finset.sum_add_distrib]

lemma potentialCurl_dilation {S : Fin 3 → Fin 3 → Coord3 → ℝ}
    (hS : ∀ i j, Differentiable ℝ (S i j)) (s r : ℝ) (c x : Coord3) (i : Fin 3) :
    potentialCurl (fun i j y => s*S i j (r • (y-c))) x i =
      s*r*potentialCurl S (r • (x-c)) i := by
  simp only [potentialCurl,direction_dilation (hS _ _),Finset.mul_sum]

lemma wedgePotential_diff {H : Coord3 → ℝ} (hH : Differentiable ℝ H) (a b i j : Fin 3) :
    Differentiable ℝ (wedgePotential a b H i j) := by
  unfold wedgePotential
  split <;> split <;> fun_prop

lemma potentialCurl_wedge {H : Coord3 → ℝ} (hH : Differentiable ℝ H) (a b : Fin 3) (x : Coord3) (i : Fin 3) :
    potentialCurl (wedgePotential a b H) x i =
      (if i=a then direction (Pi.single b 1) H x else 0) -
      (if i=b then direction (Pi.single a 1) H x else 0) :=
  wedgePotential_flux a b i hH x

lemma potentialCurl_congr_nhds {S T : Fin 3 → Fin 3 → Coord3 → ℝ} (x : Coord3)
    (h : ∀ i j, S i j =ᶠ[𝓝 x] T i j) (i : Fin 3) : potentialCurl S x i = potentialCurl T x i := by
  apply Finset.sum_congr rfl
  intro j _
  exact direction_congr_nhds (h i j) _

lemma crossingPotential_diff (L : ℝ) (a b i j : Fin 3) : Differentiable ℝ (crossingPotential L a b i j) := by
  have hf := (smooth_deriv_infty (crossingFirst_smooth L)).differentiable (by simp)
  have hg := (smooth_deriv_infty (crossingSecond_smooth L)).differentiable (by simp)
  have hF := (crossingResidualFirst_smooth L).differentiable (by simp)
  have hG := (crossingResidualSecond_smooth L).differentiable (by simp)
  apply Differentiable.add
  · apply Differentiable.add
    · exact wedgePotential_diff (by fun_prop) _ _ _ _
    · exact wedgePotential_diff (by fun_prop) _ _ _ _
  · exact wedgePotential_diff (angularStream_diff hF hG _ _) _ _ _ _

lemma crossingPotential_curl (L : ℝ) {a b : Fin 3} (ha : a≠0) (hb : b≠0) (hab : a≠b)
    (x : Coord3) (i : Fin 3) :
    potentialCurl (crossingPotential L a b) x i =
      (if i=0 then crossingCurrentZ L (x 0) (x a) (x b) else 0) +
      (if i=a then crossingCurrentX L (x 0) (x a) (x b) else 0) +
      (if i=b then crossingCurrentY L (x 0) (x a) (x b) else 0) := by
  have hf := (smooth_deriv_infty (crossingFirst_smooth L)).differentiable (by simp)
  have hg := (smooth_deriv_infty (crossingSecond_smooth L)).differentiable (by simp)
  have hF := (crossingResidualFirst_smooth L).differentiable (by simp)
  have hG := (crossingResidualSecond_smooth L).differentiable (by simp)
  let H : Coord3 → ℝ := fun y => deriv (crossingFirst L) (y 0)*sin (y a)
  let J : Coord3 → ℝ := fun y => (deriv (crossingSecond L) (y 0)/2)*sin (2*y b)
  have hH : Differentiable ℝ H := by dsimp only [H]; fun_prop
  have hJ : Differentiable ℝ J := by dsimp only [J]; fun_prop
  have hW := angularStream_diff hF hG a b
  have hdHa : direction (Pi.single a 1) H x = deriv (crossingFirst L) (x 0)*cos (x a) := by
    simpa [H,Ne.symm ha] using direction_scalar_sin hf 1 a a x
  have hdH0 : direction (Pi.single 0 1) H x = deriv (deriv (crossingFirst L)) (x 0)*sin (x a) := by
    simpa [H,ha,mul_comm] using direction_scalar_sin hf 1 0 a x
  have hg' : Differentiable ℝ (fun t => deriv (crossingSecond L) t/2) := by fun_prop
  have hgder (t : ℝ) : deriv (fun t => deriv (crossingSecond L) t/2) t =
      deriv (deriv (crossingSecond L)) t/2 := (hg t).hasDerivAt.div_const 2 |>.deriv
  have hdJb : direction (Pi.single b 1) J x = deriv (crossingSecond L) (x 0)*cos (2*x b) := by
    have hh := direction_scalar_sin hg' 2 b b x
    simp only [Ne.symm hb,ite_false,ite_true,mul_zero,add_zero] at hh
    dsimp only [J]
    rw [hh]
    ring
  have hdJ0 : direction (Pi.single 0 1) J x = deriv (deriv (crossingSecond L)) (x 0)/2*sin (2*x b) := by
    simpa only [J,hb,ite_false,ite_true,mul_zero,zero_mul,zero_add,mul_one,one_mul,hgder,mul_comm] using
      direction_scalar_sin hg' 2 0 b x
  have hx : -direction (Pi.single 0 1) H x +
      direction (Pi.single b 1) (angularStream (crossingResidualFirst L) (crossingResidualSecond L) a b) x =
      crossingCurrentX L (x 0) (x a) (x b) := by
    rw [hdH0,angularStream_b hF hG hb hab]
    unfold crossingCurrentX crossingResidualFirst
    have hc := Real.cos_two_mul (2*x b)
    have ht : 2*(2*x b)=4*x b := by ring
    rw [ht] at hc
    have hs := Real.sin_sq_add_cos_sq (2*x b)
    linear_combination
      (deriv (deriv (crossingFirst L)) (x 0)-9*crossingFirst L (x 0))*sin (x a)*hc +
      2*(deriv (deriv (crossingFirst L)) (x 0)-9*crossingFirst L (x 0))*sin (x a)*hs
  have hy : -direction (Pi.single 0 1) J x -
      direction (Pi.single a 1) (angularStream (crossingResidualFirst L) (crossingResidualSecond L) a b) x =
      crossingCurrentY L (x 0) (x a) (x b) := by
    rw [hdJ0,angularStream_a hF hG ha hab]
    unfold crossingCurrentY crossingResidualSecond
    have hs := Real.sin_two_mul (2*x b)
    have ht : 2*(2*x b)=4*x b := by ring
    rw [ht] at hs
    rw [hs]
    have hc := Real.sin_sq_add_cos_sq (x a)
    linear_combination (deriv (deriv (crossingSecond L)) (x 0)-crossingSecond L (x 0))/2*sin (2*x b)*hc
  change potentialCurl (fun i j x => wedgePotential 0 a H i j x + wedgePotential 0 b J i j x +
    wedgePotential a b (angularStream (crossingResidualFirst L) (crossingResidualSecond L) a b) i j x) x i = _
  have hHJ : ∀ i j, Differentiable ℝ (fun x => wedgePotential 0 a H i j x + wedgePotential 0 b J i j x) :=
    fun i j => (wedgePotential_diff hH 0 a i j).add (wedgePotential_diff hJ 0 b i j)
  rw [potentialCurl_add hHJ (fun i j => wedgePotential_diff hW a b i j),
    potentialCurl_add (fun i j => wedgePotential_diff hH 0 a i j) (fun i j => wedgePotential_diff hJ 0 b i j)]
  simp_rw [potentialCurl_wedge hH,potentialCurl_wedge hJ,potentialCurl_wedge hW]
  by_cases hi0 : i=0
  · subst i
    simp only [Ne.symm ha,Ne.symm hb,ite_false,ite_true,sub_zero,hdHa,hdJb,add_zero]
    rfl
  · by_cases hia : i=a
    · subst i
      simp only [ha,hab,ite_false,ite_true,zero_add,zero_sub,sub_zero,add_zero]
      exact hx
    · by_cases hib : i=b
      · subst i
        simp only [hb,Ne.symm hab,ite_false,ite_true,zero_add,zero_sub,sub_zero,add_zero]
        linarith [hy]
      · simp [hi0,hia,hib]

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

lemma cascade_dilation_coord (D k : ℝ) (m : ℕ) (x : Coord3) {a : Fin 3} (ha : a≠0) :
    ((k*2^m) • (x-cascadeCenter D k m)) a = k*2^m*x a := by
  simp [cascadeCenter,Pi.single_eq_of_ne ha]

lemma cascade_dilation_succ {k : ℝ} (hk : k≠0) (D : ℝ) (m : ℕ) (x : Coord3) :
    (k*2^(m+1)) • (x-cascadeCenter D k (m+1)) =
      (2:ℝ) • (((k*2^m) • (x-cascadeCenter D k m))-Pi.single 0 D) := by
  ext a
  by_cases ha : a=0
  · subst a
    change ((k*2^(m+1)) • (x-cascadeCenter D k (m+1))) 0 =
      2*(((k*2^m) • (x-cascadeCenter D k m)) 0-D)
    rw [cascade_dilation_time hk,cascade_dilation_time hk,cascadePhase_succ]
  · change ((k*2^(m+1)) • (x-cascadeCenter D k (m+1))) a =
      2*(((k*2^m) • (x-cascadeCenter D k m)) a-(Pi.single 0 D : Coord3) a)
    rw [cascade_dilation_coord _ _ _ _ ha,cascade_dilation_coord _ _ _ _ ha,
      Pi.single_eq_of_ne ha,pow_succ]
    ring

lemma cascadePotentialMother_wedges (L K : ℝ) (a b i j : Fin 3) (x : Coord3) :
    cascadePotentialMother L K a b i j x =
      wedgePotential 0 a (cascadeBaseStream L K a) i j x +
      wedgePotential a b (cascadeCrossStream L K a b) i j x := by
  unfold cascadePotentialMother wedgePotential
  ring

lemma wedgePotential_as_mul (a b i j : Fin 3) (H : Coord3 → ℝ) (x : Coord3) :
    wedgePotential a b H i j x =
      ((if i=a ∧ j=b then (1:ℝ) else 0)-(if j=a ∧ i=b then (1:ℝ) else 0))*H x := by
  unfold wedgePotential
  split <;> split <;> ring

lemma cascade_stage_potential_crossing {L K : ℝ} (hL : 0<L) (hK : 0<K)
    {a b : Fin 3} (ha : a≠0) (hb : b≠0) (x : Coord3)
    (hs₁ : K+2 < x 0) (hs₂ : x 0 < cascadeLength L K) (i j : Fin 3) :
    cascadePotentialMother L K a b i j x + cascadeRatio L K*
      cascadePotentialMother L K b a i j ((2:ℝ) • (x-Pi.single 0 (cascadeLength L K))) =
    (connectorProfile K (K+2)*exp (-3*L))*
      crossingPotential L a b i j (x-Pi.single 0 (K+2+L)) := by
  let y : Coord3 := x-Pi.single 0 (K+2+L)
  let z : Coord3 := (2:ℝ) • (x-Pi.single 0 (cascadeLength L K))
  have hy0 : y 0=x 0-(K+2+L) := by simp [y]
  have hya : y a=x a := by simp [y,Pi.single_eq_of_ne ha]
  have hyb : y b=x b := by simp [y,Pi.single_eq_of_ne hb]
  have hz0 : z 0=2*(x 0-cascadeLength L K) := by simp [z]
  have hzb : z b=2*x b := by simp [z,Pi.single_eq_of_ne hb]
  have hc : cascadeCrossStream L K b a z=0 := by
    apply cascadeCrossStream_zero_left hL
    rw [hz0]
    linarith
  have hbase : cascadeBaseStream L K a x =
      (connectorProfile K (K+2)*exp (-3*L))*(deriv (crossingFirst L) (y 0)*sin (y a)) := by
    rw [cascadeBaseStream,cascadeProfile_crossing_current_deriv hL hK hs₁,hy0,hya]
    ring
  have hnext : cascadeRatio L K*cascadeBaseStream L K b z =
      (connectorProfile K (K+2)*exp (-3*L))*((deriv (crossingSecond L) (y 0)/2)*sin (2*y b)) := by
    rw [cascadeBaseStream,hz0,hzb,←mul_assoc,cascadeProfile_crossing_next_deriv hL hK hs₂,hy0,hyb]
    ring
  have hcross : cascadeCrossStream L K a b x =
      (connectorProfile K (K+2)*exp (-3*L))*
      angularStream (crossingResidualFirst L) (crossingResidualSecond L) a b y := by
    simp only [cascadeCrossStream,angularStream,hy0,hya,hyb]
  change cascadePotentialMother L K a b i j x +
    cascadeRatio L K*cascadePotentialMother L K b a i j z = _
  rw [cascadePotentialMother_wedges,cascadePotentialMother_wedges]
  change _ = (connectorProfile K (K+2)*exp (-3*L))*crossingPotential L a b i j y
  simp only [crossingPotential,wedgePotential_as_mul,hc,hbase,hcross]
  linear_combination
    ((if i=0 ∧ j=b then (1:ℝ) else 0)-(if j=0 ∧ i=b then (1:ℝ) else 0))*hnext

lemma cascadePotentialTerm_crossing_pair {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (m : ℕ)
    (hs₁ : K+2 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0) < cascadeLength L K) (i j : Fin 3) :
    cascadePotentialTerm L K k A m i j x + cascadePotentialTerm L K k A (m+1) i j x =
      (A*cascadeRatio L K^m)*(connectorProfile K (K+2)*exp (-3*L))*
      crossingPotential L (cascadeAxis m) (cascadeAxis (m+1)) i j
        ((k*2^m) • (x-cascadeCenter (cascadeLength L K) k m)-Pi.single 0 (K+2+L)) := by
  have haxis : cascadeAxis (m+1+1)=cascadeAxis m := by
    simp [cascadeAxis,Nat.even_add_one]
  simp only [cascadePotentialTerm,haxis]
  rw [cascade_dilation_succ hk,pow_succ]
  have he := cascade_stage_potential_crossing hL hK (cascadeAxis_ne_zero m)
    (cascadeAxis_ne_zero (m+1)) ((k*2^m) • (x-cascadeCenter (cascadeLength L K) k m))
    (by simpa only [cascade_dilation_time hk] using hs₁)
    (by simpa only [cascade_dilation_time hk] using hs₂) i j
  linear_combination (A*cascadeRatio L K^m)*he

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

lemma direction_scalar_cos {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (r : ℝ) (i a : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => f (y 0)*cos (r*y a)) x =
      f (x 0)*(-r*sin (r*x a)*(if a=i then 1 else 0)) +
      cos (r*x a)*(deriv f (x 0)*(if (0:Fin 3)=i then 1 else 0)) := by
  rw [direction_mul (by fun_prop) (by fun_prop),direction_cos_coord,direction_scalar_coord hf]

lemma crossingValue3_diff (L : ℝ) (a b : Fin 3) : Differentiable ℝ (crossingValue3 L a b) := by
  have hf := (crossingFirst_smooth L).differentiable (by simp)
  have hg := (crossingSecond_smooth L).differentiable (by simp)
  unfold crossingValue3 crossingValue
  fun_prop

lemma crossingValue3_direction (L : ℝ) (a b i : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (crossingValue3 L a b) x =
      (if i=0 then crossingCurrentZ L (x 0) (x a) (x b) else 0) +
      (if i=a then -crossingFirst L (x 0)*sin (x a) else 0) +
      (if i=b then -2*crossingSecond L (x 0)*sin (2*x b) else 0) := by
  have hf := (crossingFirst_smooth L).differentiable (by simp)
  have hg := (crossingSecond_smooth L).differentiable (by simp)
  have he : crossingValue3 L a b = fun x =>
      crossingFirst L (x 0)*cos (1*x a)+crossingSecond L (x 0)*cos (2*x b) := by
    funext x; simp [crossingValue3,crossingValue]
  rw [he,direction_add (by fun_prop) (by fun_prop),direction_scalar_cos hf,direction_scalar_cos hg]
  simp only [one_mul,crossingCurrentZ]
  simp_rw [@eq_comm _ a i, @eq_comm _ b i, @eq_comm _ (0 : Fin 3) i]
  split_ifs <;> ring

lemma crossingTensor_mulVec (L : ℝ) (a b : Fin 3) (x v : Coord3) (i : Fin 3) :
    (crossingTensor L a b x *ᵥ v) i =
      (if i=0 then v 0 else 0) +
      (if i=a then crossingXX L (x 0) (x a) (x b)*v a+crossingXY L (x 0) (x a) (x b)*v b else 0) +
      (if i=b then crossingXY L (x 0) (x a) (x b)*v a+crossingYY L (x 0) (x a) (x b)*v b else 0) := by
  simp only [Matrix.mulVec,dotProduct,crossingTensor,add_mul,Finset.sum_add_distrib,
    ite_and,ite_mul,zero_mul]
  simp only [Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_const_zero,one_mul]
  split_ifs <;> ring

lemma crossingTensor_constitution {L : ℝ} (hL : 0<L) {a b : Fin 3}
    (ha : a≠0) (hb : b≠0) (hab : a≠b) (x : Coord3) :
    crossingTensor L a b x *ᵥ (fun i => direction (Pi.single i 1) (crossingValue3 L a b) x) =
      potentialCurl (crossingPotential L a b) x := by
  ext i
  rw [crossingTensor_mulVec,crossingPotential_curl L ha hb hab]
  simp only [crossingValue3_direction,ha,hb,Ne.symm ha,Ne.symm hb,hab,Ne.symm hab,
    ite_true,ite_false,zero_add,add_zero]
  obtain ⟨hfx,hfy⟩ := crossing_current_constitution hL (x 0) (x a) (x b)
  rw [←hfx,←hfy]

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

lemma pureModeValue_diff {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a : Fin 3) :
    Differentiable ℝ (pureModeValue f a) := by
  unfold pureModeValue
  fun_prop

lemma pureModePotential_diff {f : ℝ → ℝ} (hf : Differentiable ℝ (deriv f))
    (a i j : Fin 3) : Differentiable ℝ (pureModePotential f a i j) := by
  exact wedgePotential_diff (by fun_prop) _ _ _ _

lemma pureModeValue_direction {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (a i : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (pureModeValue f a) x =
      (if i=0 then deriv f (x 0)*cos (x a) else 0) +
      (if i=a then -f (x 0)*sin (x a) else 0) := by
  have h := direction_scalar_cos hf 1 i a x
  simp only [one_mul] at h
  unfold pureModeValue
  rw [h]
  simp_rw [@eq_comm _ a i,@eq_comm _ (0:Fin 3) i]
  split_ifs <;> ring

lemma pureModePotential_curl {f : ℝ → ℝ} (hf : Differentiable ℝ (deriv f))
    {a : Fin 3} (ha : a≠0) (x : Coord3) (i : Fin 3) :
    potentialCurl (pureModePotential f a) x i =
      (if i=0 then deriv f (x 0)*cos (x a) else 0) -
      (if i=a then deriv (deriv f) (x 0)*sin (x a) else 0) := by
  rw [pureModePotential,potentialCurl_wedge (by fun_prop)]
  have ha' := direction_scalar_sin hf 1 a a x
  have h0 := direction_scalar_sin hf 1 0 a x
  simp only [one_mul,ha,Ne.symm ha,ite_true,ite_false,mul_one,mul_zero,add_zero,zero_add] at ha' h0
  rw [ha',h0]
  ring_nf

lemma pureMode_constitution {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) {a : Fin 3} (ha : a≠0) (x : Coord3)
    (q : ℝ) (heq : deriv (deriv f) (x 0) = q*f (x 0)) :
    pureModeTensor q a *ᵥ (fun i => direction (Pi.single i 1) (pureModeValue f a) x) =
      potentialCurl (pureModePotential f a) x := by
  ext i
  rw [pureModeTensor,mulVec_diagonal]
  simp only [pureModeValue_direction hf,pureModePotential_curl hf' ha,heq]
  by_cases h0 : i=0
  · subst i
    simp [Ne.symm ha]
  · by_cases hai : i=a
    · subst i
      simp [ha]
      ring
    · simp [h0,hai]

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

lemma cascadeIndex_spec {D k : ℝ} (x : Coord3) (ht₀ : 0≤k*x 0) (ht : k*x 0<2*D) :
    0 ≤ cascadePhase D k (cascadeIndex D k x) (x 0) ∧
      cascadePhase D k (cascadeIndex D k x) (x 0)≤D := by
  have hs := Nat.find_spec (exists_cascade_index D k (x 0))
  have hu : cascadePhase D k (cascadeIndex D k x) (x 0)≤D := hs.resolve_right (not_le.mpr ht)
  refine ⟨?_,hu⟩
  cases hn : cascadeIndex D k x with
  | zero => simpa [cascadePhase_zero] using ht₀
  | succ n =>
    have hmin := Nat.find_min (exists_cascade_index D k (x 0)) (show n < cascadeIndex D k x by omega)
    have hprev : D < cascadePhase D k n (x 0) := lt_of_not_ge (fun h => hmin (Or.inl h))
    rw [cascadePhase_succ]
    linarith

lemma cascadeTensor_normal (L K k : ℝ) (x : Coord3) :
    cascadeTensor L K k x *ᵥ (Pi.single 0 1 : Coord3) = Pi.single 0 1 := by
  unfold cascadeTensor cascadeStageTensor
  split_ifs
  · exact pureModeTensor_normal (cascadeAxis_ne_zero _) _
  · exact crossingTensor_normal (cascadeAxis_ne_zero _) (cascadeAxis_ne_zero _) _ _
  · exact one_mulVec _

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_LocalConstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma direction_affineShift {f : Coord3 → ℝ} (hf : Differentiable ℝ f)
    (s r : ℝ) (c d v x : Coord3) :
    direction v (fun y => s*f (r • (y-c)-d)) x = s*r*direction v f (r • (x-c)-d) := by
  have hT : Differentiable ℝ (fun y : Coord3 => f (y-d)) := hf.comp (differentiable_id.sub_const d)
  rw [direction_dilation hT]
  have hh := direction_dilation hf 1 1 d v (r • (x-c))
  simpa only [one_mul,one_smul] using congrArg (fun z => s*r*z) hh

lemma potentialCurl_affineShift {S : Fin 3 → Fin 3 → Coord3 → ℝ}
    (hS : ∀ i j, Differentiable ℝ (S i j)) (s r : ℝ) (c d x : Coord3) (i : Fin 3) :
    potentialCurl (fun i j y => s*S i j (r • (y-c)-d)) x i =
      s*r*potentialCurl S (r • (x-c)-d) i := by
  simp only [potentialCurl,direction_affineShift (hS _ _),Finset.mul_sum]

lemma local_scaled_constitution {V v : Coord3 → ℝ}
    {T S : Fin 3 → Fin 3 → Coord3 → ℝ}
    (hv : Differentiable ℝ v) (hS : ∀ i j, Differentiable ℝ (S i j))
    (s r : ℝ) (c d x : Coord3) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hV : V =ᶠ[𝓝 x] fun y => s*v (r • (y-c)-d))
    (hT : ∀ i j, T i j =ᶠ[𝓝 x] fun y => s*S i j (r • (y-c)-d))
    (hc : A *ᵥ (fun i => direction (Pi.single i 1) v (r • (x-c)-d)) =
      potentialCurl S (r • (x-c)-d)) :
    A *ᵥ (fun i => direction (Pi.single i 1) V x) = potentialCurl T x := by
  ext i
  rw [potentialCurl_congr_nhds x hT i,potentialCurl_affineShift hS]
  have hg (j : Fin 3) : direction (Pi.single j 1) V x =
      (s*r)*direction (Pi.single j 1) v (r • (x-c)-d) := by
    rw [direction_congr_nhds hV,direction_affineShift hv]
  simp only [mulVec,dotProduct,hg]
  calc
    _ = s*r*∑ j, A i j*direction (Pi.single j 1) v (r • (x-c)-d) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    _ = _ := by rw [←hc]; rfl

lemma cascadeValue_crossing {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (m : ℕ)
    (hs₁ : K+2 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0) < cascadeLength L K) :
    cascadeValue L K k A x =
      ((A*cascadeRatio L K^m)*(connectorProfile K (K+2)*exp (-3*L)))*
      crossingValue3 L (cascadeAxis m) (cascadeAxis (m+1))
        ((k*2^m) • (x-cascadeCenter (cascadeLength L K) k m)-Pi.single 0 (K+2+L)) := by
  rw [cascadeValue_two_modes hL hK A x m (by linarith) hs₂.le]
  have h := cascade_overlap_value hL hK hs₁.le hs₂.le (A*cascadeRatio L K^m)
    (k*2^m*x (cascadeAxis m)) (k*2^m*x (cascadeAxis (m+1)))
  simp only [crossingValue3,Pi.sub_apply,Pi.single_eq_same,
    Pi.single_eq_of_ne (cascadeAxis_ne_zero m),Pi.single_eq_of_ne (cascadeAxis_ne_zero (m+1)),
    sub_zero,cascade_dilation_time hk,cascade_dilation_coord _ _ _ _ (cascadeAxis_ne_zero m),
    cascade_dilation_coord _ _ _ _ (cascadeAxis_ne_zero (m+1))]
  rw [cascadeTerm,cascadeTerm,cascadePhase_succ,pow_succ]
  convert h using 1 <;> ring_nf

lemma cascade_crossing_nhds {L K k : ℝ} (x : Coord3) (m : ℕ)
    (hs₁ : K+2 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0) < cascadeLength L K) :
    {y : Coord3 | K+2 < cascadePhase (cascadeLength L K) k m (y 0) ∧
      cascadePhase (cascadeLength L K) k m (y 0) < cascadeLength L K} ∈ 𝓝 x := by
  have hc : Continuous (fun y : Coord3 => cascadePhase (cascadeLength L K) k m (y 0)) := by
    unfold cascadePhase
    fun_prop
  exact (hc.isOpen_preimage _ isOpen_Ioo).mem_nhds ⟨hs₁,hs₂⟩

theorem cascade_crossing_constitution {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (m : ℕ)
    (hs₁ : K+2 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0) < cascadeLength L K) :
    crossingTensor L (cascadeAxis m) (cascadeAxis (m+1))
        ((k*2^m) • (x-cascadeCenter (cascadeLength L K) k m)-Pi.single 0 (K+2+L)) *ᵥ
      (fun i => direction (Pi.single i 1) (cascadeValue L K k A) x) =
      cascadeFlux L K k A x := by
  apply local_scaled_constitution (crossingValue3_diff L _ _) (crossingPotential_diff L _ _)
    ((A*cascadeRatio L K^m)*(connectorProfile K (K+2)*exp (-3*L))) (k*2^m)
    (cascadeCenter (cascadeLength L K) k m) (Pi.single 0 (K+2+L)) x
  · filter_upwards [cascade_crossing_nhds x m hs₁ hs₂] with y hy
    exact cascadeValue_crossing hL hK hk A y m hy.1 hy.2
  · intro i j
    filter_upwards [cascade_crossing_nhds x m hs₁ hs₂] with y hy
    rw [cascadePotential_two_terms hL hK hk A y (m := m) (by linarith [hy.1]) (by linarith [hy.2])]
    exact cascadePotentialTerm_crossing_pair hL hK hk A y m hy.1 hy.2 i j
  · exact crossingTensor_constitution hL (cascadeAxis_ne_zero m)
      (cascadeAxis_ne_zero (m+1)) (cascadeAxis_ne_succ m) _

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_CascadeConnectorConstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma cascadeProfile_deriv_connector {L K t : ℝ} (hL : 0<L)
    (ht₁ : 0<t) (ht₂ : t<K+2) :
    deriv (cascadeProfile L K) t = deriv (connectorProfile K) t := by
  have he : cascadeProfile L K =ᶠ[𝓝 t] connectorProfile K := by
    filter_upwards [Ioo_mem_nhds ht₁ ht₂] with r hr
    exact cascadeProfile_connector hL hr.1.le hr.2.le
  exact he.deriv_eq

lemma cascadeValue_connector {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (m : ℕ)
    (hs₁ : 0 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0)<K+2) :
    cascadeValue L K k A x =
      (A*cascadeRatio L K^m)*pureModeValue (connectorProfile K) (cascadeAxis m)
        ((k*2^m) • (x-cascadeCenter (cascadeLength L K) k m)) := by
  rw [cascadeValue_two_modes hL hK A x m hs₁.le (by have hD : cascadeLength L K = K+2+2*L := rfl; linarith)]
  simp only [cascadeTerm,cascadePhase_succ,cascadeProfile_next_connector_zero hL hs₂.le,
    mul_zero,zero_mul,add_zero,cascadeProfile_connector hL hs₁.le hs₂.le,pureModeValue,
    cascade_dilation_time hk,cascade_dilation_coord _ _ _ _ (cascadeAxis_ne_zero m)]
  ring

lemma cascadePotentialTerm_connector_pair {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (m : ℕ)
    (hs₁ : 0 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0)<K+2) (i j : Fin 3) :
    cascadePotentialTerm L K k A m i j x+ cascadePotentialTerm L K k A (m+1) i j x =
      (A*cascadeRatio L K^m)*pureModePotential (connectorProfile K) (cascadeAxis m) i j
        ((k*2^m) • (x-cascadeCenter (cascadeLength L K) k m)) := by
  let y : Coord3 := (k*2^m) • (x-cascadeCenter (cascadeLength L K) k m)
  let z : Coord3 := (k*2^(m+1)) • (x-cascadeCenter (cascadeLength L K) k (m+1))
  have hy : y 0 = cascadePhase (cascadeLength L K) k m (x 0) := cascade_dilation_time hk _ _ _
  have hz : z 0 = 2*(y 0-cascadeLength L K) := by
    rw [←cascade_dilation_time hk] at hs₁
    dsimp only [z]
    rw [cascade_dilation_time hk,cascadePhase_succ,←hy]
  have hc : cascadeCrossStream L K (cascadeAxis m) (cascadeAxis (m+1)) y=0 :=
    cascadeCrossStream_zero_left hL _ _ _ (by rw [hy]; linarith)
  have hnext : cascadeBaseStream L K (cascadeAxis (m+1)) z=0 := by
    apply cascadeBaseStream_zero hL
    left
    rw [hz,hy]
    have hD : cascadeLength L K = K+2+2*L := rfl
    linarith
  have hcnext : cascadeCrossStream L K (cascadeAxis (m+1)) (cascadeAxis (m+1+1)) z=0 := by
    apply cascadeCrossStream_zero_left hL
    rw [hz,hy]
    have hD : cascadeLength L K = K+2+2*L := rfl
    linarith
  have hb : cascadeBaseStream L K (cascadeAxis m) y =
      deriv (connectorProfile K) (y 0)*sin (y (cascadeAxis m)) := by
    rw [cascadeBaseStream,cascadeProfile_deriv_connector hL (by rw [hy]; exact hs₁)
      (by rw [hy]; exact hs₂)]
  change (A*cascadeRatio L K^m)*cascadePotentialMother L K _ _ i j y+
    (A*cascadeRatio L K^(m+1))*cascadePotentialMother L K _ _ i j z = _
  simp only [cascadePotentialMother,hc,hnext,hcnext,hb,mul_zero,add_zero,
    pureModePotential,wedgePotential,ite_self,sub_self]
  rfl

lemma cascade_connector_nhds {L K k : ℝ} (x : Coord3) (m : ℕ)
    (hs₁ : 0 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0)<K+2) :
    {y : Coord3 | 0 < cascadePhase (cascadeLength L K) k m (y 0) ∧
      cascadePhase (cascadeLength L K) k m (y 0)<K+2} ∈ 𝓝 x := by
  have hc : Continuous (fun y : Coord3 => cascadePhase (cascadeLength L K) k m (y 0)) := by
    unfold cascadePhase
    fun_prop
  exact (hc.isOpen_preimage _ isOpen_Ioo).mem_nhds ⟨hs₁,hs₂⟩

theorem cascade_connector_constitution {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (m : ℕ)
    (hs₁ : 0 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0)<K+2) :
    pureModeTensor (connectorAngular K (cascadePhase (cascadeLength L K) k m (x 0))) (cascadeAxis m) *ᵥ
      (fun i => direction (Pi.single i 1) (cascadeValue L K k A) x) = cascadeFlux L K k A x := by
  have hf := (connectorProfile_smooth K).differentiable (by simp)
  have hf' := (smooth_deriv_infty (connectorProfile_smooth K)).differentiable (by simp)
  apply local_scaled_constitution (pureModeValue_diff hf _) (pureModePotential_diff hf' _)
    (A*cascadeRatio L K^m) (k*2^m) (cascadeCenter (cascadeLength L K) k m) 0 x
  · filter_upwards [cascade_connector_nhds x m hs₁ hs₂] with y hy
    simpa only [sub_zero] using cascadeValue_connector hL hK hk A y m hy.1 hy.2
  · intro i j
    filter_upwards [cascade_connector_nhds x m hs₁ hs₂] with y hy
    rw [cascadePotential_two_terms hL hK hk A y (m := m) (by linarith [hy.1])
      (by have hh : K+2 < cascadeLength L K := by unfold cascadeLength; linarith
          linarith [hy.2]) i j]
    simpa only [sub_zero] using cascadePotentialTerm_connector_pair hL hK hk A y m hy.1 hy.2 i j
  · apply pureMode_constitution hf hf' (cascadeAxis_ne_zero m)
    simp only [sub_zero,cascade_dilation_time hk,connectorAngular]
    rw [div_mul_cancel₀ _ (connectorProfile_pos K _).ne']

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_CascadeConstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma ae_coord3_ne (i : Fin 3) (r : ℝ) : ∀ᵐ x : Coord3, x i≠r := by
  exact MeasureTheory.Measure.ae_eval_ne (fun _ : Fin 3 => (volume : Measure ℝ)) i r

lemma ae_cascadePhase_ne {k : ℝ} (hk : k≠0) (D r : ℝ) (n : ℕ) :
    ∀ᵐ x : Coord3, cascadePhase D k n (x 0)≠r := by
  filter_upwards [ae_coord3_ne 0 ((r-2*D+2^n*(2*D))/(2^n*k))] with x hx
  intro he
  apply hx
  apply (eq_div_iff (mul_ne_zero (by positivity) hk)).mpr
  unfold cascadePhase at he
  nlinarith

lemma cascadeValue_direction_terminal {L K k : ℝ} (hL : 0<L) (hK : 0<K)
    (A : ℝ) (x : Coord3) (ht : 2*cascadeLength L K<k*x 0) (i : Fin 3) :
    direction (Pi.single i 1) (cascadeValue L K k A) x=0 := by
  have hn : {y : Coord3 | 2*cascadeLength L K<k*y 0} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (continuous_const.mul (continuous_apply 0))).mem_nhds ht
  have he : cascadeValue L K k A =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [hn] with y hy
    exact cascadeValue_terminal hL hK A y hy.le
  simp [direction,he.fderiv_eq]

theorem cascadeTensor_constitution_ae {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) : ∀ᵐ x : Coord3, 0≤k*x 0 →
      cascadeTensor L K k x *ᵥ (fun i => direction (Pi.single i 1) (cascadeValue L K k A) x) =
        cascadeFlux L K k A x := by
  have h0 : ∀ᵐ x : Coord3, ∀ n : ℕ, cascadePhase (cascadeLength L K) k n (x 0)≠0 :=
    ae_all_iff.mpr (fun n => ae_cascadePhase_ne hk _ _ n)
  have hD : ∀ᵐ x : Coord3, ∀ n : ℕ, cascadePhase (cascadeLength L K) k n (x 0)≠cascadeLength L K :=
    ae_all_iff.mpr (fun n => ae_cascadePhase_ne hk _ _ n)
  have hK2 : ∀ᵐ x : Coord3, ∀ n : ℕ, cascadePhase (cascadeLength L K) k n (x 0)≠K+2 :=
    ae_all_iff.mpr (fun n => ae_cascadePhase_ne hk _ _ n)
  have ht : ∀ᵐ x : Coord3, k*x 0≠2*cascadeLength L K := by
    simpa only [cascadePhase_zero] using ae_cascadePhase_ne hk (cascadeLength L K) (2*cascadeLength L K) 0
  filter_upwards [h0,hD,hK2,ht] with x hx0 hxD hxK hxt
  intro hx
  by_cases hterm : k*x 0<2*cascadeLength L K
  · have hs := cascadeIndex_spec x hx hterm
    have hs₁ := lt_of_le_of_ne hs.1 (Ne.symm (hx0 _))
    have hs₂ := lt_of_le_of_ne hs.2 (hxD _)
    rw [cascadeTensor,ite_eq_left ⟨hx,hterm⟩,cascadeStageTensor]
    split_ifs with hc
    · exact cascade_connector_constitution hL hK hk A x _ hs₁ hc
    · exact cascade_crossing_constitution hL hK hk A x _
        (lt_of_le_of_ne (le_of_not_gt hc) (Ne.symm (hxK _))) hs₂
  · have ht' : 2*cascadeLength L K<k*x 0 := lt_of_le_of_ne (le_of_not_gt hterm) (Ne.symm hxt)
    have hz (i : Fin 3) := cascadeValue_direction_terminal hL hK A x ht' i
    ext i
    rw [cascadeFlux_terminal_strict hL hK hk A x ht' i]
    simp [Matrix.mulVec,dotProduct,hz]

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

lemma initialConnectorRate_left {a b K t : ℝ} (hK : 0 < K) (ht : t ≤ 1) :
    initialConnectorRate a b K t=a := by
  rw [initialConnectorRate,smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hK.le),mul_zero,add_zero]

lemma initialConnectorRate_right {a b K t : ℝ} (hK : 0 < K) (ht : K+1 ≤ t) :
    initialConnectorRate a b K t=b := by
  rw [initialConnectorRate,smoothTransition.one_of_one_le
    ((le_div_iff₀ hK).mpr (by linarith))]
  ring

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

lemma initialConnectorProfile_second (a b K t : ℝ) :
    deriv (deriv (initialConnectorProfile a b K)) t=
      ((initialConnectorRate a b K t)^2-deriv (initialConnectorRate a b K) t)*
        initialConnectorProfile a b K t := by
  have he : deriv (initialConnectorProfile a b K)=
      fun t => -initialConnectorRate a b K t*initialConnectorProfile a b K t :=
    funext fun t => (initialConnectorProfile_hasDerivAt a b K t).deriv
  rw [he]
  have h := (((initialConnectorRate_smooth a b K).differentiable (by simp) t).hasDerivAt.neg).mul
    (initialConnectorProfile_hasDerivAt a b K t)
  simp only [Pi.mul_def,Pi.neg_def] at h
  rw [h.deriv]
  ring

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

lemma initialConnector_constitution (a b K : ℝ) {i : Fin 3} (hi : i ≠ 0) (x : Coord3) :
    pureModeTensor (initialConnectorAngular a b K (x 0)) i*ᵥ
      (fun j => direction (Pi.single j 1) (pureModeValue (initialConnectorProfile a b K) i) x)=
        potentialCurl (pureModePotential (initialConnectorProfile a b K) i) x := by
  apply pureMode_constitution ((initialConnectorProfile_smooth a b K).differentiable (by simp))
    ((smooth_deriv_infty (initialConnectorProfile_smooth a b K)).differentiable (by simp)) hi
  exact initialConnectorProfile_second a b K (x 0)

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

lemma axial_paste_eventually_right {E F : Type*} [TopologicalSpace E]
    {f g : E → F} {t : E → ℝ} {c : ℝ} (ht : Continuous t) {x : E} (hx : c<t x) :
    (fun y => if t y < c then f y else g y)=ᶠ[𝓝 x] g := by
  filter_upwards [(isOpen_lt continuous_const ht).mem_nhds hx] with y hy
  exact ite_eq_right (not_lt.mpr hy.le)

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

lemma finiteEndingPotential_antisymm (a J L K : ℝ) (i j : Fin 3) :
    finiteEndingPotential a J L K i j=fun x => -finiteEndingPotential a J L K j i x := by
  funext x
  unfold finiteEndingPotential
  split_ifs
  · unfold pureModePotential wedgePotential
    ring
  · exact congrFun (cascadePotential_antisymm L K 1 _ i j) _

lemma finiteEndingValue_initial {a J L K : ℝ} (hJ : 0 < J) (x : Coord3) (hx : x 0 ≤ 1) :
    finiteEndingValue a J L K x=exp (-a*x 0)*cos (x 1) := by
  rw [finiteEndingValue,ite_eq_left (show x 0<J+2 by linarith),pureModeValue,
    initialConnectorProfile_left hJ hx]

lemma direction_translate {f : Coord3 → ℝ} (hf : Differentiable ℝ f)
    (c v x : Coord3) : direction v (fun y => f (y-c)) x=direction v f (x-c) := by
  simpa only [one_mul,one_smul] using direction_dilation hf 1 1 c v x

lemma potentialCurl_translate {S : Fin 3 → Fin 3 → Coord3 → ℝ}
    (hS : ∀ i j,Differentiable ℝ (S i j)) (c x : Coord3) (i : Fin 3) :
    potentialCurl (fun i j y => S i j (y-c)) x i=potentialCurl S (x-c) i := by
  simpa only [one_mul,one_smul] using potentialCurl_dilation hS 1 1 c x i

lemma finiteEndingTensor_normal (a J L K : ℝ) (x : Coord3) :
    finiteEndingTensor a J L K x*ᵥPi.single 0 1=Pi.single 0 1 := by
  unfold finiteEndingTensor
  split_ifs
  · exact pureModeTensor_normal (by decide : (1:Fin 3)≠0) _
  · exact cascadeTensor_normal _ _ _ _

lemma finiteEnding_constitution_left (a J L K : ℝ) (x : Coord3) (hx : x 0<J+2) :
    finiteEndingTensor a J L K x*ᵥ(fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)=
      potentialCurl (finiteEndingPotential a J L K) x := by
  have hv : finiteEndingValue a J L K=ᶠ[𝓝 x] pureModeValue (initialConnectorProfile a (1/2) J) 1 :=
    axial_paste_eventually_left (continuous_apply 0) hx
  have hp (i j : Fin 3) : finiteEndingPotential a J L K i j=ᶠ[𝓝 x]
      pureModePotential (initialConnectorProfile a (1/2) J) 1 i j :=
    axial_paste_eventually_left (continuous_apply 0) hx
  have hg : (fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)=
      (fun j => direction (Pi.single j 1) (pureModeValue (initialConnectorProfile a (1/2) J) 1) x) :=
    funext fun j => direction_congr_nhds hv _
  rw [finiteEndingTensor,ite_eq_left hx,hg]
  rw [initialConnector_constitution a (1/2) J (by decide)]
  ext i
  exact (potentialCurl_congr_nhds x hp i).symm

lemma finiteEnding_constitution_right {a J L K : ℝ} (_ : 0<J) (hL : 1≤L) (hK : 0<K)
    (x : Coord3) (hx : J+2<x 0)
    (hc : cascadeTensor L K 1 (x-Pi.single 0 (J+2))*ᵥ
      (fun j => direction (Pi.single j 1) (cascadeValue L K 1 (initialConnectorProfile a (1/2) J (J+2)))
        (x-Pi.single 0 (J+2)))=
      cascadeFlux L K 1 (initialConnectorProfile a (1/2) J (J+2)) (x-Pi.single 0 (J+2))) :
    finiteEndingTensor a J L K x*ᵥ(fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)=
      potentialCurl (finiteEndingPotential a J L K) x := by
  have hv : finiteEndingValue a J L K=ᶠ[𝓝 x]
      (fun y => cascadeValue L K 1 (initialConnectorProfile a (1/2) J (J+2)) (y-Pi.single 0 (J+2))) :=
    axial_paste_eventually_right (continuous_apply 0) hx
  have hp (i j : Fin 3) : finiteEndingPotential a J L K i j=ᶠ[𝓝 x]
      (fun y => cascadePotential L K 1 (initialConnectorProfile a (1/2) J (J+2)) i j (y-Pi.single 0 (J+2))) :=
    axial_paste_eventually_right (continuous_apply 0) hx
  have hg : (fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)=
      (fun j => direction (Pi.single j 1) (cascadeValue L K 1 (initialConnectorProfile a (1/2) J (J+2)))
        (x-Pi.single 0 (J+2))) := by
    funext j
    rw [direction_congr_nhds hv _]
    exact direction_translate ((cascadeValue_C2 hL hK (by norm_num) _).differentiable (by norm_num)) _ _ _
  rw [finiteEndingTensor,ite_eq_right (not_lt.mpr hx.le),hg,hc]
  ext i
  rw [potentialCurl_congr_nhds x hp i,potentialCurl_translate
    (fun i j => (cascadePotential_C2 hL hK 1 _ i j).differentiable (by norm_num))]
  rfl

lemma finiteEnding_constitution_ae {a J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ∀ᵐ x : Coord3, finiteEndingTensor a J L K x*ᵥ
      (fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)=
        potentialCurl (finiteEndingPotential a J L K) x := by
  have he := (measurePreserving_add_right (volume : Measure Coord3) (-Pi.single 0 (J+2))).quasiMeasurePreserving.ae
    (cascadeTensor_constitution_ae (lt_of_lt_of_le (by norm_num) hL) hK (by norm_num : (1:ℝ)≠0)
      (initialConnectorProfile a (1/2) J (J+2)))
  simp only [←sub_eq_add_neg] at he
  filter_upwards [he,ae_coord3_ne 0 (J+2)] with x hx hn
  rcases lt_or_gt_of_ne hn with hl|hr
  · exact finiteEnding_constitution_left a J L K x hl
  · apply finiteEnding_constitution_right hJ hL hK x hr (hx ?_)
    simp only [one_mul,Pi.sub_apply,Pi.single_eq_same]
    linarith

end

open Real Set Filter Topology MeasureTheory Matrix

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

lemma direction_permutedDilation {f : Coord3 → ℝ} (hf : Differentiable ℝ f)
    (e : Equiv.Perm (Fin 3)) (r : ℝ) (i : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y => f (permutedDilation e r y)) x =
      r*direction (Pi.single (e.symm i) 1) f (permutedDilation e r x) := by
  let P : Coord3 →L[ℝ] Coord3 :=
    ContinuousLinearMap.pi (fun j => r • ContinuousLinearMap.proj (e j))
  have hP : (P : Coord3 → Coord3)=permutedDilation e r := rfl
  have he : P (Pi.single i 1)=r • Pi.single (e.symm i) 1 := by
    ext j
    simp only [P,ContinuousLinearMap.pi_apply,_root_.smul_apply,
      ContinuousLinearMap.proj_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp only [show e j=i ↔ j=e.symm i from e.eq_symm_apply.symm]
  have hd := (hf (P x)).hasFDerivAt.comp x P.hasFDerivAt
  change fderiv ℝ (f ∘ P) x (Pi.single i 1)=_
  rw [hd.fderiv,ContinuousLinearMap.comp_apply,he,map_smul,smul_eq_mul]
  rfl

lemma potentialCurl_permutedDilation {S : Fin 3 → Fin 3 → Coord3 → ℝ}
    (hS : ∀ i j,Differentiable ℝ (S i j))
    (e : Equiv.Perm (Fin 3)) (r : ℝ) (x : Coord3) (i : Fin 3) :
    potentialCurl (fun i j y => S (e.symm i) (e.symm j) (permutedDilation e r y)) x i =
      r*potentialCurl S (permutedDilation e r x) (e.symm i) := by
  simp only [potentialCurl,direction_permutedDilation (hS _ _),Finset.mul_sum]
  exact e.symm.sum_comp (fun j => r*direction (Pi.single j 1) (S (e.symm i) j) (permutedDilation e r x))

lemma permutedTensor_constitution {f : Coord3 → ℝ} (hf : Differentiable ℝ f)
    {S : Fin 3 → Fin 3 → Coord3 → ℝ} (hS : ∀ i j,Differentiable ℝ (S i j))
    (A : Coord3 → Mat3) (e : Equiv.Perm (Fin 3)) (r : ℝ) (x : Coord3)
    (h : A (permutedDilation e r x)*ᵥ(fun j => direction (Pi.single j 1) f (permutedDilation e r x))=
      potentialCurl S (permutedDilation e r x)) :
    (fun i j => A (permutedDilation e r x) (e.symm i) (e.symm j))*ᵥ
      (fun j => direction (Pi.single j 1) (fun y => f (permutedDilation e r y)) x)=
      potentialCurl (fun i j y => S (e.symm i) (e.symm j) (permutedDilation e r y)) x := by
  ext i
  rw [potentialCurl_permutedDilation hS]
  simp only [Matrix.mulVec,dotProduct,direction_permutedDilation hf]
  have hh := congrFun h (e.symm i)
  change (∑ j,A (permutedDilation e r x) (e.symm i) j*direction (Pi.single j 1) f (permutedDilation e r x))=
    potentialCurl S (permutedDilation e r x) (e.symm i) at hh
  rw [←hh,Finset.mul_sum]
  calc
    _ = ∑ j,r*(A (permutedDilation e r x) (e.symm i) (e.symm j)*
        direction (Pi.single (e.symm j) 1) f (permutedDilation e r x)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := Equiv.sum_comp e.symm (fun j => r*(A (permutedDilation e r x) (e.symm i) j*
      direction (Pi.single j 1) f (permutedDilation e r x)))

lemma permutedDilation_quasiMeasurePreserving (e : Equiv.Perm (Fin 3)) {r : ℝ} (hr : r≠0) :
    Measure.QuasiMeasurePreserving (permutedDilation e r) volume volume := by
  have hp := (volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ) e.symm).quasiMeasurePreserving
  have hs := Measure.quasiMeasurePreserving_smul (volume : Measure Coord3) hr
  convert hs.comp hp using 1
  all_goals try with_reducible_and_instances rfl
  funext x i
  simp [permutedDilation,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]

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

lemma alignedEndingPotential_antisymm (lam k J L K : ℝ) (i j : Fin 3) :
    alignedEndingPotential lam k J L K i j = fun x => -alignedEndingPotential lam k J L K j i x := by
  funext x
  exact congrFun (finiteEndingPotential_antisymm _ _ _ _ _ _) _

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

lemma alignedEnding_constitution_ae {lam k J L K : ℝ} (hk : k≠0) (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ∀ᵐ x : Coord3,alignedEndingTensor lam k J L K x*ᵥ
      (fun j => direction (Pi.single j 1) (alignedEndingValue lam k J L K) x)=
      potentialCurl (alignedEndingPotential lam k J L K) x := by
  have hh := (permutedDilation_quasiMeasurePreserving angularAxisSwap hk).ae
    (finiteEnding_constitution_ae (a:=lam/k) hJ hL hK)
  filter_upwards [hh] with x hx
  exact permutedTensor_constitution ((finiteEndingValue_C2 hJ hL hK).differentiable (by norm_num))
    (fun i j => (finiteEndingPotential_C2 hJ hL hK i j).differentiable (by norm_num))
    (finiteEndingTensor (lam/k) J L K) angularAxisSwap k x hx

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_AxialPairRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma axialPair_gradient_zero {f : Coord3 → ℝ} {x : Coord3}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    (gradientColumns (fderiv ℝ (axialPair f) x)).col 0 i=if (0:Fin 3)=i then 1 else 0 := by
  have hd (j : Fin 2) : DifferentiableAt ℝ (fun x => axialPair f x j) x := by
    fin_cases j
    · exact (differentiable_apply 0).differentiableAt
    · exact hf
  simp only [gradientColumns,Matrix.col,transpose_apply,LinearMap.toMatrix'_apply,
    ContinuousLinearMap.coe_coe,fderiv_pi hd,ContinuousLinearMap.pi_apply]
  exact direction_coord i 0 x

lemma axialPair_gradient_one {f : Coord3 → ℝ} {x : Coord3}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    (gradientColumns (fderiv ℝ (axialPair f) x)).col 1 i=direction (Pi.single i 1) f x := by
  have hd (j : Fin 2) : DifferentiableAt ℝ (fun x => axialPair f x j) x := by
    fin_cases j
    · exact (differentiable_apply 0).differentiableAt
    · exact hf
  simp only [gradientColumns,Matrix.col,transpose_apply,LinearMap.toMatrix'_apply,
    ContinuousLinearMap.coe_coe,fderiv_pi hd,ContinuousLinearMap.pi_apply]
  rfl

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

lemma endingJoin_overlap {u : Coord3 → Fin 2 → ℝ} {lam k J L K : ℝ}
    (hk : 0<k) (hJ : 0<J)
    (hu : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)])
    {x : Coord3} (hx : x 0∈Icc (6:ℝ) 7) :
    u=ᶠ[𝓝 x] axialPair (delayedEndingValue lam k J L K 7) := by
  have h1 : ∀ᶠ y : Coord3 in 𝓝 x,4<y 0 :=
    (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds (show 4<x 0 by linarith [hx.1])
  have h2 : ∀ᶠ y : Coord3 in 𝓝 x,k*(y 0-7)<1 :=
    (isOpen_lt (continuous_const.mul ((continuous_apply 0).sub continuous_const)) continuous_const).mem_nhds (show k*(x 0-7)<1 by
      have hh := mul_nonpos_of_nonneg_of_nonpos hk.le (sub_nonpos.mpr hx.2)
      linarith)
  filter_upwards [h1,h2] with y hy1 hy2
  rw [hu y hy1.le]
  simp only [axialPair,delayedEndingValue_initial_of_bound hk hJ y hy2.le]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AEFluxWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

theorem C1_divergence_zero_ae_test
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (μ : Measure E) [μ.IsAddHaarMeasure] (v : ι → E) (F : ι → E → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i))
    (ψ : SmoothScalar E) (hc : HasCompactSupport ψ.val)
    (hdiv : ∀ᵐ x ∂μ, x∈Function.support ψ.val → ∑ i, direction (v i) (F i) x = 0) :
    (∫ x, ∑ i, F i x*(smoothDirection (v i) ψ).val x ∂μ) = 0 := by
  have hp := smoothScalar_contDiff ψ
  have hI (i : ι) : Integrable (fun x => F i x*(smoothDirection (v i) ψ).val x) μ :=
    ((hF i).continuous.mul (smoothScalar_contDiff (smoothDirection (v i) ψ)).continuous).integrable_of_hasCompactSupport
      (compactSupport_smoothDirection (v i) hc).mul_left
  have hI' (i : ι) : Integrable (fun x => ψ.val x*direction (v i) (F i) x) μ :=
    (hp.continuous.mul (direction_continuous (hF i) _)).integrable_of_hasCompactSupport hc.mul_right
  have hibp (i : ι) : (∫ x, F i x*(smoothDirection (v i) ψ).val x ∂μ) =
      -(∫ x, ψ.val x*direction (v i) (F i) x ∂μ) := by
    have hh := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.mul ℝ ℝ)
      (f := F i) (g := ψ.val) (v := v i)
      (show Integrable (fun x => direction (v i) (F i) x*ψ.val x) μ by
        simpa only [mul_comm] using hI' i)
      (hI i)
      (((hF i).continuous.mul hp.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (fun x _ => ((hF i).differentiable (by norm_num) x).hasFDerivAt)
      (fun x _ => (hp.differentiable (by simp) x).hasFDerivAt)
    change (∫ x, F i x * (fderiv ℝ ψ.val x) (v i) ∂μ) =
      -(∫ x, (fderiv ℝ (F i) x) (v i) * ψ.val x ∂μ) at hh
    simpa only [direction,smoothDirection_apply,mul_comm] using hh
  rw [integral_finsetSum _ (fun i _ => hI i)]
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib,←integral_finsetSum _ (fun i _ => hI' i)]
  have hz : (fun x => ∑ i, ψ.val x*direction (v i) (F i) x) =ᵐ[μ] fun _ => (0:ℝ) := by
    filter_upwards [hdiv] with x hxdiv
    rw [←Finset.mul_sum]
    by_cases hx : x∈Function.support ψ.val
    · rw [hxdiv hx,mul_zero]
    · rw [Function.notMem_support.mp hx,zero_mul]
  rw [integral_congr_ae hz,integral_zero,neg_zero]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AxialFluxBlend
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
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

lemma axialFluxBlend_divergence {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {F G : Coord3 → Coord3}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (x : Coord3) :
    coordinateDivergence (axialFluxBlend χ F G) x=
      (1-χ (x 0))*coordinateDivergence F x+χ (x 0)*coordinateDivergence G x+
        deriv χ (x 0)*(G x 0-F x 0) := by
  have hf (i : Fin 3) : DifferentiableAt ℝ (fun y => F y i) x := differentiableAt_pi.mp (hF x) i
  have hg (i : Fin 3) : DifferentiableAt ℝ (fun y => G y i) x := differentiableAt_pi.mp (hG x) i
  have hc : DifferentiableAt ℝ (fun y : Coord3 => χ (y 0)) x :=
    (hχ (x 0)).comp x (differentiableAt_apply 0 x)
  have hd (i : Fin 3) : direction (Pi.single i 1) (fun y => axialFluxBlend χ F G y i) x=
      (1-χ (x 0))*direction (Pi.single i 1) (fun y => F y i) x+
      χ (x 0)*direction (Pi.single i 1) (fun y => G y i) x+
      deriv χ (x 0)*(if (0:Fin 3)=i then 1 else 0)*(G x i-F x i) := by
    have h1 : DifferentiableAt ℝ (fun y => 1-χ (y 0)) x := differentiableAt_const (1:ℝ) |>.sub hc
    have h2 : DifferentiableAt ℝ (fun y => (1-χ (y 0))*F y i) x := h1.mul (hf i)
    have h3 : DifferentiableAt ℝ (fun y => χ (y 0)*G y i) x := hc.mul (hg i)
    change direction (Pi.single i 1) (fun y => (1-χ (y 0))*F y i+χ (y 0)*G y i) x=_
    rw [direction_add h2 h3,direction_mul h1 (hf i),direction_mul hc (hg i),
      direction_sub (differentiableAt_const (1:ℝ)) hc,direction_scalar_coord hχ i 0,direction_const]
    ring
  change (∑ i,direction (Pi.single i 1) (fun y => axialFluxBlend χ F G y i) x)=_
  simp_rw [hd]
  simp only [Fin.sum_univ_three,coordinateDivergence,show (0:Fin 3)≠1 by decide,
    show (0:Fin 3)≠2 by decide,ite_true,ite_false,mul_one,mul_zero,zero_mul,add_zero]
  change _=(1-χ (x 0))*(direction (Pi.single 0 1) (fun y => F y 0) x+
    direction (Pi.single 1 1) (fun y => F y 1) x+direction (Pi.single 2 1) (fun y => F y 2) x)+
    χ (x 0)*(direction (Pi.single 0 1) (fun y => G y 0) x+
    direction (Pi.single 1 1) (fun y => G y 1) x+direction (Pi.single 2 1) (fun y => G y 2) x)+_
  ring

lemma axialFluxBlend_divergence_zero {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {F G : Coord3 → Coord3}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) {x : Coord3}
    (hFd : coordinateDivergence F x=0) (hGd : coordinateDivergence G x=0)
    (hn : deriv χ (x 0)=0 ∨ F x 0=G x 0) :
    coordinateDivergence (axialFluxBlend χ F G) x=0 := by
  rw [axialFluxBlend_divergence hχ hF hG,hFd,hGd,mul_zero,mul_zero,zero_add,zero_add]
  rcases hn with hn|hn
  · rw [hn,zero_mul]
  · rw [hn,sub_self,mul_zero]

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma delayedEndingPotential_C2 {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (i j : Fin 3) :
    ContDiff ℝ 2 (delayedEndingPotential lam k J L K R i j) :=
  contDiff_const.mul ((alignedEndingPotential_C2 hJ hL hK i j).comp (contDiff_id.sub contDiff_const))

lemma delayedEndingPotential_antisymm (lam k J L K R : ℝ) (i j : Fin 3) :
    delayedEndingPotential lam k J L K R i j=fun x => -delayedEndingPotential lam k J L K R j i x := by
  funext x
  rw [delayedEndingPotential,alignedEndingPotential_antisymm]
  simp [delayedEndingPotential]

lemma delayedEnding_direction {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (v x : Coord3) :
    direction v (delayedEndingValue lam k J L K R) x=
      exp (-lam*R)*direction v (alignedEndingValue lam k J L K) (x-Pi.single 0 R) := by
  unfold delayedEndingValue
  simpa only [one_smul,mul_one] using (direction_dilation
    ((alignedEndingValue_C2 (lam:=lam) (k:=k) hJ hL hK).differentiable (by norm_num))
    (exp (-lam*R)) 1 (Pi.single 0 R) v x)

lemma delayedEnding_curl {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (x : Coord3) (i : Fin 3) :
    potentialCurl (delayedEndingPotential lam k J L K R) x i=
      exp (-lam*R)*potentialCurl (alignedEndingPotential lam k J L K) (x-Pi.single 0 R) i := by
  unfold delayedEndingPotential
  simpa only [one_smul,mul_one] using (potentialCurl_dilation
    (fun i j => (alignedEndingPotential_C2 (lam:=lam) (k:=k) hJ hL hK i j).differentiable (by norm_num))
    (exp (-lam*R)) 1 (Pi.single 0 R) x i)

lemma delayedEnding_constitution_ae {lam k J L K R : ℝ} (hk : k≠0) (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ∀ᵐ x : Coord3,delayedEndingTensor lam k J L K R x*ᵥ
      (fun i => direction (Pi.single i 1) (delayedEndingValue lam k J L K R) x)=
      potentialCurl (delayedEndingPotential lam k J L K R) x := by
  have hh := (measurePreserving_add_right (volume : Measure Coord3) (-Pi.single 0 R)).quasiMeasurePreserving.ae
    (alignedEnding_constitution_ae (lam:=lam) hk hJ hL hK)
  filter_upwards [hh] with x hx
  simp only [←sub_eq_add_neg] at hx
  ext i
  simp only [delayedEnding_direction hJ hL hK,delayedEnding_curl hJ hL hK]
  change (delayedEndingTensor lam k J L K R x*ᵥ(exp (-lam*R) •
    (fun j => direction (Pi.single j 1) (alignedEndingValue lam k J L K) (x-Pi.single 0 R)))) i=_
  rw [Matrix.mulVec_smul,delayedEndingTensor,hx]
  rfl

lemma delayedEndingFlux_C1 {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ContDiff ℝ 1 (potentialCurl (delayedEndingPotential lam k J L K R)) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.sum
  intro j _
  exact direction_C1 (delayedEndingPotential_C2 hJ hL hK i j) _

lemma delayedEndingFlux_divergence {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (x : Coord3) :
    coordinateDivergence (potentialCurl (delayedEndingPotential lam k J L K R)) x=0 :=
  antisymmetric_potential_divergence (fun i => Pi.single i 1) (delayedEndingPotential lam k J L K R)
    (delayedEndingPotential_C2 hJ hL hK) (delayedEndingPotential_antisymm lam k J L K R) x

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_DelayedPairFlux
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real

lemma matrix_product_col_eq_mulVec {m n l : Type*} [Fintype n]
    (A : Matrix m n ℝ) (B : Matrix n l ℝ) (j : l) : (A*B).col j=A*ᵥB.col j := rfl

lemma delayedPairFlux_C1 {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (j : Fin 2) :
    ContDiff ℝ 1 (delayedPairFlux lam k J L K R j) := by
  unfold delayedPairFlux
  split_ifs
  · exact contDiff_const
  · exact delayedEndingFlux_C1 hJ hL hK

lemma delayedPairFlux_divergence {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (j : Fin 2) (x : Coord3) :
    coordinateDivergence (delayedPairFlux lam k J L K R j) x=0 := by
  unfold delayedPairFlux
  split_ifs
  · simp [coordinateDivergence]
  · exact delayedEndingFlux_divergence hJ hL hK x

lemma delayedPairFlux_constitution_ae {lam k J L K R : ℝ} (hk : k≠0) (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ∀ᵐ x : Coord3,∀ j : Fin 2,
      (delayedEndingTensor lam k J L K R x*gradientColumns
        (fderiv ℝ (axialPair (delayedEndingValue lam k J L K R)) x)).col j=delayedPairFlux lam k J L K R j x := by
  filter_upwards [delayedEnding_constitution_ae (lam:=lam) (R:=R) hk hJ hL hK] with x hx
  have hd := (delayedEndingValue_C2 (lam:=lam) (k:=k) (R:=R) hJ hL hK).differentiable (by norm_num) x
  intro j
  rw [matrix_product_col_eq_mulVec]
  fin_cases j
  · change delayedEndingTensor lam k J L K R x*ᵥ(gradientColumns (fderiv ℝ (axialPair (delayedEndingValue lam k J L K R)) x)).col 0=Pi.single 0 1
    have hh : (gradientColumns (fderiv ℝ (axialPair (delayedEndingValue lam k J L K R)) x)).col 0=Pi.single 0 1 := by
      funext i
      simpa only [Pi.single_apply,eq_comm] using axialPair_gradient_zero hd i
    rw [hh]
    exact alignedEndingTensor_normal _ _ _ _ _ _
  · change delayedEndingTensor lam k J L K R x*ᵥ(gradientColumns (fderiv ℝ (axialPair (delayedEndingValue lam k J L K R)) x)).col 1=potentialCurl (delayedEndingPotential lam k J L K R) x
    have hh : (gradientColumns (fderiv ℝ (axialPair (delayedEndingValue lam k J L K R)) x)).col 1=
        fun i => direction (Pi.single i 1) (delayedEndingValue lam k J L K R) x :=
      funext (axialPair_gradient_one hd)
    rw [hh]
    exact hx

end ScalarConductivity

end
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

lemma endingJoinCutoff_left {t : ℝ} (ht : t≤6) : endingJoinCutoff t=0 :=
  smoothTransition.zero_of_nonpos (by linarith)

lemma endingJoinCutoff_right {t : ℝ} (ht : 7≤t) : endingJoinCutoff t=1 :=
  smoothTransition.one_of_one_le (by linarith)

lemma endingJoinCutoff_deriv_zero {t : ℝ} (ht : t∉Icc (6:ℝ) 7) : deriv endingJoinCutoff t=0 := by
  have he : t<6 ∨ 7<t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases he with he|he
  · have hh : endingJoinCutoff=ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds he] with y hy
      exact endingJoinCutoff_left hy.le
    rw [hh.deriv_eq,deriv_const]
  · have hh : endingJoinCutoff=ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds he] with y hy
      exact endingJoinCutoff_right hy.le
    rw [hh.deriv_eq,deriv_const]

lemma normal_flux_of_symm {A : Mat3} (hA : A.IsSymm) (hn : A*ᵥPi.single 0 1=Pi.single 0 1) (v : Coord3) :
    (A*ᵥv) 0=v 0 := by
  have h (i : Fin 3) : A i 0=if i=0 then 1 else 0 := by
    have hh := congrFun hn i
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_three,Pi.single_apply] using hh
  have hs (i : Fin 3) : A 0 i=A i 0 := congrFun (congrFun hA i) 0
  simp [Matrix.mulVec,dotProduct,hs,h]

lemma flatBackgroundTensor_normal (s : Fin 3 → ℝ) :
    flatBackgroundTensor s*ᵥPi.single 0 1=Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [flatBackgroundTensor,Matrix.mulVec,dotProduct,Pi.single_apply]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_EndingJoinConstitution
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

lemma endingJoin_normal_ae {D : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    {s : Fin 3 → ℝ} {lam k J L K : ℝ} (hk : 0<k) (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
    (hu : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)])
    (hD : ∀ x : Coord3,x 0∈Icc (6:ℝ) 7 → D x=flatBackgroundTensor s) :
    ∀ᵐ x : Coord3,∀ j : Fin 2,
      deriv endingJoinCutoff (x 0)=0 ∨ matchingFlux D u j x 0=delayedPairFlux lam k J L K 7 j x 0 := by
  filter_upwards [delayedPairFlux_constitution_ae (lam:=lam) (R:=7) hk.ne' hJ hL hK] with x hx
  intro j
  by_cases hb : x 0∈Icc (6:ℝ) 7
  · right
    have he := endingJoin_overlap (L:=L) (K:=K) hk hJ hu hb
    rw [←hx j,matchingFlux,hD x hb,matrix_product_col_eq_mulVec,matrix_product_col_eq_mulVec,
      normal_flux_of_symm (flatBackgroundTensor_symm s) (flatBackgroundTensor_normal s)]
    rw [show delayedEndingTensor lam k J L K 7 x=alignedEndingTensor lam k J L K (x-Pi.single 0 7) from rfl,
      normal_flux_of_symm (alignedEndingTensor_symm _ _ _ _ _ _) (alignedEndingTensor_normal _ _ _ _ _ _),he.fderiv_eq]
  · exact Or.inl (endingJoinCutoff_deriv_zero hb)

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

theorem matchedEnding_weak_equation_oai {D : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hD : ContDiff ℝ (↑(⊤:ℕ∞)) D) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {s : Fin 3 → ℝ} {lam k J L K : ℝ} (hk : 0<k) (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
    (hum : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)])
    (hDm : ∀ x : Coord3,x 0∈Icc (6:ℝ) 7 → D x=flatBackgroundTensor s)
    (hPDE : ∀ j x,0<x 0 → symmetricSource D u j x=0)
    (j : Fin 2) (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val)
    (hs : tsupport ψ.val ⊆ {x : Coord3 | 0<x 0}) :
    Integrable (fun x => ∑ i,(endingJoinTensor D lam k J L K x*gradientColumns
      (fderiv ℝ (matchedEndingPair u lam k J L K) x)).col j i*(smoothDirection (Pi.single i 1) ψ).val x) ∧
    (∫ x,∑ i,(endingJoinTensor D lam k J L K x*gradientColumns
      (fderiv ℝ (matchedEndingPair u lam k J L K) x)).col j i*(smoothDirection (Pi.single i 1) ψ).val x)=0 := by
  have hF := joinedFlux_C1 (lam:=lam) (k:=k) hD hu hJ hL hK j
  have he : (fun x => ∑ i,(endingJoinTensor D lam k J L K x*gradientColumns
      (fderiv ℝ (matchedEndingPair u lam k J L K) x)).col j i*(smoothDirection (Pi.single i 1) ψ).val x)=ᵐ[volume]
      (fun x => ∑ i,joinedFlux D u lam k J L K j x i*(smoothDirection (Pi.single i 1) ψ).val x) := by
    filter_upwards [endingJoin_constitution_ae (D:=D) hk hJ hL hK hum] with x hx
    rw [hx j]
  constructor
  · apply Integrable.congr _ he.symm
    apply integrable_finsetSum
    intro i _
    exact ((contDiff_pi.mp hF i).continuous.mul
      (smoothScalar_contDiff (smoothDirection (Pi.single i 1) ψ)).continuous).integrable_of_hasCompactSupport
      (compactSupport_smoothDirection (Pi.single i 1) hc).mul_left
  · rw [integral_congr_ae he]
    apply C1_divergence_zero_ae_test volume (fun i => Pi.single i 1)
      (fun i x => joinedFlux D u lam k J L K j x i) (fun i => contDiff_pi.mp hF i) ψ hc
    filter_upwards [endingJoin_normal_ae hk hJ hL hK hum hDm] with x hx
    intro hxs
    have hp := hs (subset_tsupport _ hxs)
    exact axialFluxBlend_divergence_zero (endingJoinCutoff_smooth.differentiable (by simp))
      ((symmetricFlux_smooth hD hu j).differentiable (by simp))
      ((delayedPairFlux_C1 hJ hL hK j).differentiable (by norm_num))
      (hPDE j x hp) (delayedPairFlux_divergence hJ hL hK j x) (hx j)

end ScalarConductivity

end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.matchedEnding_weak_equation_oai := @OAI.ScalarConductivity.matchedEnding_weak_equation_oai
