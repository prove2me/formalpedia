-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketLatticeData.source_assigned_selector_mask_good_set
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T19:59:38.927995+00:00
-- url     : https://prove2.me/submissions/febb7552-d6fa-41dc-adc2-c94f9f096462

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_eventually_assigned_top_selector_concentration_of_supported

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SincMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual even sinc-product mask from (src-8), including its
quadratic approximation to one and the stated logarithmic-scale error. -/

noncomputable section

namespace LipschitzHilbert

theorem abs_one_sub_sinc_le (x : ℝ) : |1-Real.sinc x| ≤ x^2/6 := by
  by_cases hx : x = 0
  · simp [hx]
  rw [Real.sinc_of_ne_zero hx,
    show 1-Real.sin x/x = (x-Real.sin x)/x by field_simp, abs_div]
  apply (div_le_iff₀ (abs_pos.mpr hx)).mpr
  calc
    _ ≤ |x|^3/6 := Real.abs_sub_sin_le x
    _ = x^2/6*|x| := by rw [← sq_abs]; ring

theorem abs_one_sub_sinc_product_le (x y : ℝ) :
    |1-Real.sinc x*Real.sinc y| ≤ (x^2+y^2)/6 := by
  calc
    _ = |(1-Real.sinc x)+Real.sinc x*(1-Real.sinc y)| := by congr 1; ring
    _ ≤ |1-Real.sinc x|+|Real.sinc x*(1-Real.sinc y)| := abs_add_le _ _
    _ = |1-Real.sinc x|+|Real.sinc x| * |1-Real.sinc y| := by rw [abs_mul]
    _ ≤ x^2/6+1*(y^2/6) := add_le_add (abs_one_sub_sinc_le x)
      (mul_le_mul (Real.abs_sinc_le_one x) (abs_one_sub_sinc_le y) (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem abs_one_sub_sincProductMask (n : ℕ) (x y : ℝ) :
    |1-sincProductMask n x y| ≤ (n:ℝ)/3*(x^2+y^2) := by
  have hz : |Real.sinc x*Real.sinc y| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_sinc_le_one x) (Real.abs_sinc_le_one y)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have h := abs_pow_sub_pow_le (a := (1:ℝ)) (b := Real.sinc x*Real.sinc y) (n := 2*n)
  simp only [one_pow, abs_one, max_eq_left hz, mul_one, Nat.cast_mul, Nat.cast_ofNat] at h
  have hb := mul_le_mul_of_nonneg_right (abs_one_sub_sinc_product_le x y)
    (show (0:ℝ) ≤ 2*(n:ℝ) by positivity)
  exact h.trans (by convert hb using 1; ring)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopMaskApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript mask at its actual scale. Inside the prescribed
near region its error is at most a fixed constant times L^(1-A). -/

noncomputable section

namespace LipschitzHilbert

theorem topSincMask_nonneg (L A x y : ℝ) : 0 ≤ topSincMask L A x y :=
  sincProductMask_nonneg _ _ _

theorem topSincMask_le_one (L A x y : ℝ) : topSincMask L A x y ≤ 1 :=
  sincProductMask_le_one _ _ _

theorem topSincMask_error_le_one (L A x y : ℝ) : |1-topSincMask L A x y| ≤ 1 := by
  rw [abs_of_nonneg (sub_nonneg.mpr (topSincMask_le_one L A x y))]
  linarith [topSincMask_nonneg L A x y]

theorem abs_one_sub_sincProductMask_scaled (n : ℕ) (T x y : ℝ) (hT : 0 < T)
    (hx : x^2 ≤ T) (hy : y^2 ≤ T) :
    |1-sincProductMask n (x/T) (y/T)| ≤ 2*(n:ℝ)/(3*T) := by
  have hb (z : ℝ) (hz : z^2 ≤ T) : (z/T)^2 ≤ 1/T := by
    rw [div_pow]
    calc
      z^2/T^2 ≤ T/T^2 := div_le_div_of_nonneg_right hz (sq_nonneg T)
      _ = 1/T := by field_simp
  calc
    _ ≤ (n:ℝ)/3*((x/T)^2+(y/T)^2) := abs_one_sub_sincProductMask _ _ _
    _ ≤ (n:ℝ)/3*(1/T+1/T) := mul_le_mul_of_nonneg_left
      (add_le_add (hb x hx) (hb y hy)) (by positivity)
    _ = _ := by ring

theorem topSincMask_near_error (L A x y : ℝ) (hL : 1 ≤ L)
    (hx : |x| ≤ L^(A/2)) (hy : |y| ≤ L^(A/2)) :
    |1-topSincMask L A x y| ≤ (4/3:ℝ)*L^(1-A) := by
  have hL0 : 0 < L := by linarith
  have hT : 0 < L^A := Real.rpow_pos_of_pos hL0 _
  have hpow : (L^(A/2))^2 = L^A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1
    ring
  have hx2 : x^2 ≤ L^A := by
    rw [← hpow, ← sq_abs x]
    exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hy2 : y^2 ≤ L^A := by
    rw [← hpow, ← sq_abs y]
    exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hn : (⌈L⌉₊:ℝ) ≤ 2*L := by
    have hc := Nat.ceil_lt_add_one hL0.le
    linarith
  calc
    _ ≤ 2*(⌈L⌉₊:ℝ)/(3*L^A) := abs_one_sub_sincProductMask_scaled _ _ _ _ hT hx2 hy2
    _ ≤ 2*(2*L)/(3*L^A) := div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = (4/3:ℝ)*L^(1-A) := by rw [Real.rpow_sub hL0, Real.rpow_one]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MaskComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative comparison of a finite top synthesis with its actual
sinc-masked version. The near and far estimates use the same fixed
polynomial top envelope. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem norm_sum_sub_mask_le {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ι → E) (mask weight : ι → ℝ) (T ε : ℝ) (_hT : 0 ≤ T) (_hε : 0 ≤ ε)
    (hw : ∀ i, 0 ≤ weight i)
    (hF : ∀ i, ‖F i‖ ≤ T*(weight i)^8)
    (hmask : ∀ i, |1-mask i| *T*(weight i)^7 ≤ ε) :
    ‖(∑ i, F i)-(∑ i, mask i • F i)‖ ≤ ε*∑ i, weight i := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖F i-mask i • F i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ε*weight i := by
      apply Finset.sum_le_sum
      intro i _
      rw [show F i-mask i • F i = (1-mask i) • F i by module,
        norm_smul, Real.norm_eq_abs]
      calc
        _ ≤ |1-mask i| *(T*(weight i)^8) :=
          mul_le_mul_of_nonneg_left (hF i) (abs_nonneg _)
        _ = (|1-mask i| *T*(weight i)^7)*weight i := by ring
        _ ≤ ε*weight i := mul_le_mul_of_nonneg_right (hmask i) (hw i)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem topSincMask_near_far (L A x y h T ε H : ℝ) (hL : 1 ≤ L)
    (hh : 0 ≤ h) (hT : 0 ≤ T) (_hε : 0 ≤ ε) (_hH : 0 ≤ H)
    (hhH : h ≤ H)
    (hnear : (4/3:ℝ)*L^(1-A)*T*H^7 ≤ ε)
    (hfar : (¬ (|x| ≤ L^(A/2) ∧ |y| ≤ L^(A/2))) → T*h^7 ≤ ε) :
    |1-topSincMask L A x y| *T*h^7 ≤ ε := by
  by_cases hxy : |x| ≤ L^(A/2) ∧ |y| ≤ L^(A/2)
  · have hm := topSincMask_near_error L A x y hL hxy.1 hxy.2
    have hp := pow_le_pow_left₀ hh hhH 7
    calc
      _ ≤ ((4/3:ℝ)*L^(1-A))*T*H^7 := by
        gcongr
      _ ≤ ε := hnear
  · calc
      _ ≤ 1*T*h^7 := by
        gcongr
        exact topSincMask_error_le_one L A x y
      _ = T*h^7 := by ring
      _ ≤ ε := hfar hxy

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact top shape from (src-5) and its seventh-power decay
outside the mask's near region. -/

noncomputable section

namespace LipschitzHilbert

theorem topShape_nonneg (K D x y : ℝ) (hK : 0 < K) : 0 ≤ topShape K D x y := by
  unfold topShape
  positivity

theorem topShape_le (K D x y : ℝ) (hK : 0 < K) (hD : 0 ≤ D) :
    topShape K D x y ≤ (2:ℝ)^D := by
  have hb : 1 ≤ 1+(|x|+|y|)/K := le_add_of_nonneg_right
    (div_nonneg (add_nonneg (abs_nonneg x) (abs_nonneg y)) hK.le)
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hb (neg_nonpos.mpr hD)
  exact (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by norm_num) D)).trans_eq (mul_one _)

theorem topShape_far_seventh (L A A1 D x y : ℝ) (hL : 0 < L) (hD : 0 ≤ D)
    (hfar : ¬ (|x| ≤ L^(A/2) ∧ |y| ≤ L^(A/2))) :
    (topShape (L^A1) D x y)^7 ≤
      ((2:ℝ)^D)^7*L^(-7*D*(A/2-A1)) := by
  have hK : 0 < L^A1 := Real.rpow_pos_of_pos hL _
  have hdist : L^(A/2) ≤ |x|+|y| := by
    by_contra h
    apply hfar
    constructor <;> linarith [abs_nonneg x, abs_nonneg y]
  have hbase : L^(A/2-A1) ≤ 1+(|x|+|y|)/(L^A1) := by
    rw [Real.rpow_sub hL]
    have h := div_le_div_of_nonneg_right hdist hK.le
    linarith
  have hb : 0 ≤ 1+(|x|+|y|)/(L^A1) := by positivity
  have heq : (topShape (L^A1) D x y)^7 =
      ((2:ℝ)^D)^7*(1+(|x|+|y|)/(L^A1))^(-7*D) := by
    unfold topShape
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
    congr 1
    ring
  rw [heq]
  have hp := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hL (A/2-A1)) hbase
    (show -7*D ≤ 0 by linarith)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Real.rpow_mul hL.le]
  congr 1
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MaskParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the mask exponent after the fixed top bounds. Both the
near-region and far-region errors have any prescribed polynomial decay. -/

noncomputable section

namespace LipschitzHilbert

theorem constant_mul_rpow_le (L M a b : ℝ) (hL : 1 ≤ L) (hM : M ≤ L)
    (hab : a+1 ≤ b) : M*L^a ≤ L^b := by
  have hL0 : 0 < L := by linarith
  calc
    _ ≤ L*L^a := mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hL0.le _)
    _ = L^(a+1) := by rw [Real.rpow_add hL0, Real.rpow_one]; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL hab

theorem top_mask_error_of_exponents (L C H A A1 D x y : ℝ)
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hlarge : (4/3:ℝ)*((2:ℝ)^D)^7 ≤ L)
    (hnear : C+H+2 ≤ A) (hfar : C+H+1 ≤ 7*D*(A/2-A1)) :
    |1-topSincMask L A x y| * L^C * (topShape (L^A1) D x y)^7 ≤ L^(-H) := by
  have hL0 : 0 < L := by linarith
  let B := ((2:ℝ)^D)^7
  have hB : 0 ≤ B := by positivity
  have hBL : B ≤ L := by dsimp [B] at *; nlinarith
  apply topSincMask_near_far L A x y (topShape (L^A1) D x y) (L^C) (L^(-H)) ((2:ℝ)^D)
    hL (topShape_nonneg _ _ _ _ (Real.rpow_pos_of_pos hL0 _)) (by positivity) (by positivity)
    (by positivity) (topShape_le _ _ _ _ (Real.rpow_pos_of_pos hL0 _) hD)
  · have hn := constant_mul_rpow_le L ((4/3:ℝ)*B) (C+1-A) (-H) hL hlarge (by linarith)
    convert hn using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [B]
    rw [show C+1-A = (1-A)+C by ring, Real.rpow_add hL0]
    ring
  · intro hxy
    have hs := topShape_far_seventh L A A1 D x y hL0 hD hxy
    have hp := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hL0.le C)
    have hf := constant_mul_rpow_le L B (C-7*D*(A/2-A1)) (-H) hL hBL (by linarith)
    apply hp.trans
    convert hf using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [B]
    rw [show C-7*D*(A/2-A1) = C+(-7*D*(A/2-A1)) by ring, Real.rpow_add hL0]
    ring

theorem exists_mask_parameters_above (C H A1 D M : ℝ)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hD : 0 < D) :
    ∃ A L0 : ℝ, M < A ∧ 2 < A ∧ 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ x y : ℝ,
      |1-topSincMask L A x y| * L^C * (topShape (L^A1) D x y)^7 ≤ L^(-H) := by
  let A := max (M+1) (max (C+H+3) (2*A1+2*(C+H+2)/(7*D)))
  let L0 := max 1 ((4/3:ℝ)*((2:ℝ)^D)^7)
  have hM : M+1 ≤ A := le_max_left _ _
  have hA1 : C+H+3 ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hA2 : 2*A1+2*(C+H+2)/(7*D) ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hfar : C+H+1 ≤ 7*D*(A/2-A1) := by
    have heq : (2*(C+H+2)/(7*D))*(7*D) = 2*(C+H+2) := by field_simp
    have hp := mul_le_mul_of_nonneg_right hA2 (show 0 ≤ 7*D by positivity)
    nlinarith
  refine ⟨A,L0,by linarith,by linarith,le_max_left _ _,?_⟩
  intro L hL x y
  exact top_mask_error_of_exponents L C H A A1 D x y
    ((le_max_left _ _).trans hL) hD.le ((le_max_right _ _).trans hL) (by linarith) hfar

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual decaying top weights and their motion along a reference line. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem radius_nonnegative (T : SlopeBox) (z : ℝ × ℝ) : 0 ≤ T.radius z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem weight_pos (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) (z : ℝ × ℝ) :
    0 < T.weight K D z := by
  unfold weight
  have hr := T.radius_nonnegative z
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) D)
    (Real.rpow_pos_of_pos (by positivity) _)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeightIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and exact area scaling for the actual decaying top weights. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

theorem planeDivide_apply (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (z : ℝ × ℝ) :
    planeDivide a b ha hb z = (z.1 / a, z.2 / b) := by
  rfl

theorem map_planeDivide (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Measure.map (planeDivide a b ha hb) (volume.prod volume) =
      (ENNReal.ofReal |a| * ENNReal.ofReal |b|) • (volume.prod volume) := by
  have hmap (c : ℝ) (hc : c ≠ 0) :
      Measure.map (fun x : ℝ => x * c⁻¹) volume = ENNReal.ofReal |c| • volume := by
    simpa only [smul_eq_mul, Module.finrank_self, pow_one, inv_inv, mul_comm] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) (inv_ne_zero hc))
  change Measure.map (Prod.map (fun x => x * a⁻¹) (fun y => y * b⁻¹)) _ = _
  rw [← Measure.map_prod_map volume volume (by fun_prop) (by fun_prop), hmap a ha, hmap b hb,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

theorem integrable_planeDivide (f : ℝ × ℝ → ℝ)
    (hf : Integrable f (volume.prod volume)) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (fun z => f (planeDivide a b ha hb z)) (volume.prod volume) := by
  apply (integrable_map_equiv (planeDivide a b ha hb) f).mp
  rw [map_planeDivide]
  exact hf.smul_measure (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

theorem topProfile_nonnegative (D : ℝ) (z : ℝ × ℝ) : 0 ≤ topProfile D z :=
  Real.rpow_nonneg (by positivity) _

theorem topProfile_continuous (D : ℝ) : Continuous (topProfile D) := by
  unfold topProfile
  apply Continuous.rpow_const (by fun_prop)
  intro z
  left
  positivity

/-- The fixed normalized profile is integrable once its decay exponent exceeds
its two-dimensional domain. -/
theorem topProfile_integrable {D : ℝ} (hD : 2 < D) :
    Integrable (topProfile D) (volume.prod volume) := by
  have hd : (Module.finrank ℝ (ℝ × ℝ) : ℝ) < D := by simpa using hD
  have h := integrable_one_add_norm (μ := (volume.prod volume)) hd
  apply h.mono' (topProfile_continuous D).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (topProfile_nonnegative D z)]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  simp only [Prod.norm_def, Real.norm_eq_abs]
  have hmax : max |z.1| |z.2| ≤ |z.1| + |z.2| :=
    max_le (by linarith [abs_nonneg z.2]) (by linarith [abs_nonneg z.1])
  linarith

namespace SlopeBox

theorem normalizedCoordinates_eq (T : SlopeBox) (K : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.normalizedCoordinates K hK z = (T.horizontal z / K, T.transverse z / K) := by
  ext <;> simp [normalizedCoordinates, planeDivide_apply, slopeShear, horizontal, transverse]
  <;> ring

theorem weight_eq_topProfile (T : SlopeBox) (K D : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.weight K D z = 2 ^ D * topProfile D (T.normalizedCoordinates K hK z) := by
  rw [normalizedCoordinates_eq]
  simp only [weight, topProfile, radius, abs_div, abs_of_pos hK, add_div]

/-- The actual top weight is integrable, uniformly over positions and slopes. -/
theorem weight_integrable (T : SlopeBox) {K D : ℝ} (hK : 0 < K) (hD : 2 < D) :
    Integrable (T.weight K D) (volume.prod volume) := by
  have hf := integrable_planeDivide (topProfile D) (topProfile_integrable hD)
    (K * T.length) (K * T.width)
    (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne')
  have hs := (slopeShear_measurePreserving (-T.slope)).integrable_comp_of_integrable hf
  have ht := hs.comp_sub_right (T.x, T.y)
  have heq : T.weight K D = fun z => 2 ^ D *
      ((fun z => topProfile D (planeDivide (K * T.length) (K * T.width)
        (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)) ∘
        slopeShear (-T.slope)) (z - (T.x, T.y)) := by
    funext z
    exact T.weight_eq_topProfile K D hK z
  rw [heq]
  exact ht.const_mul _

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeBoxMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sinc mask in the manuscript's actual slope coordinates, with
parameters fixed uniformly before choosing the finite top family. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
namespace SlopeBox

theorem mask_continuous (T : SlopeBox) (L A : ℝ) : Continuous (T.mask L A) := by
  unfold mask topSincMask sincProductMask horizontal transverse
  apply Continuous.pow
  apply Continuous.mul
  · apply Real.continuous_sinc.comp
    fun_prop
  · apply Real.continuous_sinc.comp
    fun_prop

theorem weight_continuous (T : SlopeBox) (K D : ℝ) (hK : 0 < K) : Continuous (T.weight K D) := by
  unfold weight radius horizontal transverse
  apply Continuous.mul continuous_const
  apply Continuous.rpow_const
  · fun_prop
  · intro z
    left
    have h : 0 ≤ |(z.1-T.x)/T.length|+|((z.2-T.y)-T.slope*(z.1-T.x))/T.width| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    positivity

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopDyadicDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic dilation domination for the actual decaying top weights. The
base dilation may be larger than the weight radius, as required when the
popular-rectangle argument first clips to the localization strip. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert
namespace SlopeBox

theorem measurableSet_radialDilation (T : SlopeBox) (R : ℝ) :
    MeasurableSet (T.radialDilation R) := by
  apply measurableSet_le _ measurable_const
  unfold radius horizontal transverse
  fun_prop

theorem exists_dyadic_weight_bound (T : SlopeBox) (K R D : ℝ)
    (hK : 0 < K) (hKR : K ≤ R) (hD : 0 ≤ D) (z : ℝ × ℝ) :
    ∃ n : ℕ, z ∈ T.radialDilation (R*2^n) ∧
      T.weight K D z ≤ 4^D*(2^(-D))^n := by
  have hR : 0 < R := hK.trans_le hKR
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hfour : (4 : ℝ)^D = (2 : ℝ)^D*(2:ℝ)^D := by
    rw [← Real.mul_rpow htwo.le htwo.le]
    norm_num
  by_cases hz : T.radius z < R
  · refine ⟨0, by simpa [radialDilation] using hz.le, ?_⟩
    simp only [pow_zero, mul_one]
    have hw : T.weight K D z ≤ (2:ℝ)^D := by
      unfold weight
      calc
        _ ≤ (2:ℝ)^D * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos (by
            exact le_add_of_nonneg_right (div_nonneg (T.radius_nonnegative z) hK.le)) (by linarith)) (by positivity)
        _ = _ := mul_one _
    apply hw.trans
    rw [hfour]
    exact le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow (by norm_num) hD)
  · have hratio : 1 ≤ T.radius z/R := (le_div_iff₀ hR).mpr (by simpa using le_of_not_gt hz)
    obtain ⟨n, hn, hn1⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ)<2)
    refine ⟨n+1, ?_, ?_⟩
    · exact (div_lt_iff₀ hR).mp hn1 |>.le.trans_eq (mul_comm _ _)
    · have hlo : (2:ℝ)^n ≤ 1+T.radius z/K := by
        have hnon := T.radius_nonnegative z
        have hdiv : T.radius z/R ≤ T.radius z/K :=
          div_le_div_of_nonneg_left hnon hK hKR
        linarith
      have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ)<2^n) hlo
        (by linarith : -D ≤ 0)
      calc
        T.weight K D z ≤ (2:ℝ)^D*((2:ℝ)^n)^(-D) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = (2:ℝ)^D*(2^(-D))^n := by
          rw [← Real.rpow_natCast_mul htwo.le, mul_comm (n:ℝ), Real.rpow_mul_natCast htwo.le]
        _ = 4^D*(2^(-D))^(n+1) := by
          rw [hfour, pow_succ]
          have hc : (2:ℝ)^D*2^(-D) = 1 := by
            rw [← Real.rpow_add htwo]; simp
          symm
          calc
            _ = ((2:ℝ)^D*2^(-D))*((2:ℝ)^D*(2^(-D))^n) := by ring
            _ = _ := by rw [hc, one_mul]

theorem weight_le_dyadic_sum (T : SlopeBox) (K R D : ℝ)
    (hK : 0 < K) (hKR : K ≤ R) (hD : 0 ≤ D) (z : ℝ × ℝ) :
    ENNReal.ofReal (T.weight K D z) ≤
      ∑' n : ℕ, ENNReal.ofReal (4^D*(2^(-D))^n) *
        (T.radialDilation (R*2^n)).indicator (fun _ => (1:ℝ≥0∞)) z := by
  obtain ⟨n, hn, hweight⟩ := T.exists_dyadic_weight_bound K R D hK hKR hD z
  exact (ENNReal.ofReal_le_ofReal hweight).trans (by
    simpa only [indicator_of_mem hn, mul_one] using
      (ENNReal.le_tsum (f := fun m : ℕ => ENNReal.ofReal (4^D*(2^(-D))^m) *
          (T.radialDilation (R*2^m)).indicator (fun _ => (1:ℝ≥0∞)) z) n :
        ENNReal.ofReal (4^D*(2^(-D))^n) *
          (T.radialDilation (R*2^n)).indicator (fun _ => (1:ℝ≥0∞)) z ≤ _))

end SlopeBox
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PublishedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published inputs for the Lipschitz-direction Hilbert transform

The two classical estimates used by the manuscript are stated as propositions.
Their deterministic consequences make the quantifiers needed for the
finite rectangle and martingale applications explicit.

* Lacey--Li, *On a conjecture of E. M. Stein on the Hilbert transform on
  vector fields*, Memoirs AMS 205 (2010), no. 965, result 1.10 and equation
  (1.11); DOI 10.1090/S0065-9266-10-00572-7. In the author version
  arXiv:0704.0808 these occur on printed p. 3, with the finite-family proof
  in Chapter 3. This is the published form of arXiv:math/0601213v2,
  Theorem 1.4. We use the finite admissible-rectangle weak `(2,2)` estimate.
* Zorin-Kranich, *Weighted Lépingle inequality*, Bernoulli 26 (2020),
  2311--2318, Theorem 1.1, with `p = 2`, `r = 3`, and weight one.
  We use only real-valued finite martingales on probability spaces.

The deterministic consequences below make the quantifiers relevant to the
application explicit: a union of high-average rectangles, and a variation
sum whose increasing indices may be chosen separately at each point.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert

/-- Disjoint popularity witnesses turn a covering bound into a weighted packing
bound. In the manuscript, `w i` is a top rectangle's area and `a` its
popularity lower bound. -/
theorem disjoint_witness_packing {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (E R : ι → Set Ω) (w : ι → ℝ≥0∞) (a : ℝ≥0∞)
    (hmeas : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (hsub : ∀ i, E i ⊆ R i) (hsize : ∀ i, a * w i ≤ μ (E i)) :
    a * ∑ i, w i ≤ μ (⋃ i, R i) := by
  classical
  calc
    a * ∑ i, w i = ∑ i, a * w i := Finset.mul_sum _ _ _
    _ ≤ ∑ i, μ (E i) := Finset.sum_le_sum fun i _ => hsize i
    _ = μ (⋃ i, E i) := by rw [measure_iUnion hdisj hmeas, tsum_fintype]
    _ ≤ μ (⋃ i, R i) := measure_mono (Set.iUnion_mono hsub)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeOrthonormal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthonormal long and transverse axes of an actual slope box. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem slopeAxes_apply (s : ℝ) (i : Fin 2) : slopeAxes s i = slopeAxisVectors s i := by
  exact congrFun (OrthonormalBasis.coe_mk _ _) i

theorem slopeAxes_repr_zero (s : ℝ) (z : Plane) :
    (slopeAxes s).repr z 0 = (z 0+s*z 1)/Real.sqrt (1+s^2) := by
  rw [OrthonormalBasis.repr_apply_apply, slopeAxes_apply]
  simp [slopeAxisVectors, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem slopeAxes_repr_one (s : ℝ) (z : Plane) :
    (slopeAxes s).repr z 1 = (z 1-s*z 0)/Real.sqrt (1+s^2) := by
  rw [OrthonormalBasis.repr_apply_apply, slopeAxes_apply]
  simp [slopeAxisVectors, PiLp.inner_apply, Fin.sum_univ_two]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlaneCoordinates
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measure-preserving bridge from the manuscript's real coordinate
pairs to the Euclidean plane used by the published maximal estimate. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem planeCoordinates_measurePreserving :
    MeasurePreserving planeCoordinates (volume.prod volume) volume := by
  exact (PiLp.volume_preserving_toLp (Fin 2)).comp
    (measurePreserving_finTwoArrow (volume : Measure ℝ)).symm

theorem planeCoordinates_image_measure (s : Set (ℝ × ℝ)) :
    volume (planeCoordinates '' s) = (volume.prod volume) s := by
  have h := planeCoordinates_measurePreserving.measure_preimage_equiv (planeCoordinates '' s)
  rw [Set.preimage_image_eq s planeCoordinates.injective] at h
  exact h.symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectangleArea
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact area of the orthogonal rectangles in the published input. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

theorem orthogonalCoordinates_apply (R : Rectangle) (z : Plane) :
    R.orthogonalCoordinates z = (R.axes.repr (z-R.center) 0, R.axes.repr (z-R.center) 1) := rfl

theorem orthogonalCoordinates_measurePreserving (R : Rectangle) :
    MeasurePreserving R.orthogonalCoordinates volume (volume.prod volume) := by
  exact planeCoordinates_measurePreserving.symm.comp
    (R.axes.measurePreserving_repr.comp (measurePreserving_sub_right volume R.center))

theorem carrier_eq_coordinate_rectangle (R : Rectangle) :
    R.carrier = R.orthogonalCoordinates ⁻¹'
      (Icc (-R.long/2) (R.long/2) ×ˢ Icc (-R.short/2) (R.short/2)) := by
  ext z
  simp only [carrier, mem_ofPred_eq, mem_preimage, mem_prod, mem_Icc,
    orthogonalCoordinates_apply, abs_le, neg_div]

theorem volume_carrier (R : Rectangle) :
    volume R.carrier = ENNReal.ofReal R.long * ENNReal.ofReal R.short := by
  rw [carrier_eq_coordinate_rectangle,
    R.orthogonalCoordinates_measurePreserving.measure_preimage_equiv,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  congr 2 <;> ring

theorem volume_carrier_ne_top (R : Rectangle) : volume R.carrier ≠ ∞ := by
  rw [volume_carrier]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem volume_carrier_pos (R : Rectangle) : 0 < volume R.carrier := by
  rw [volume_carrier]
  have hl := lt_of_lt_of_le R.short_pos R.short_le_long
  exact bot_lt_iff_ne_bot.mpr (mul_ne_zero
    (ne_of_gt (ENNReal.ofReal_pos.mpr hl))
    (ne_of_gt (ENNReal.ofReal_pos.mpr R.short_pos)))

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SlopeRectangle
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual Euclidean rectangle enclosing a clipped thin slope
parallelogram, with the explicit lengths used in the popular-top proof. -/

noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert

theorem mem_slopeRectangle (c z : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hx : |z.1-c.1| ≤ a/2) (hy : |(z.2-c.2)-s*(z.1-c.1)| ≤ b/2) :
    planeCoordinates z ∈ (slopeRectangle c s a b ha hb hba).carrier := by
  have hqpos : 0 < Real.sqrt (1+s^2) := Real.sqrt_pos.mpr (by positivity)
  have hq2 := Real.sq_sqrt (by positivity : 0 ≤ 1+s^2)
  have heq : ((z.1-c.1)+s*(z.2-c.2))/Real.sqrt (1+s^2) =
      Real.sqrt (1+s^2)*(z.1-c.1)+
        (s/Real.sqrt (1+s^2))*((z.2-c.2)-s*(z.1-c.1)) := by
    field_simp
    rw [hq2]
    ring
  change |(slopeAxes s).repr (planeCoordinates z-planeCoordinates c) 0| ≤ _ ∧
    |(slopeAxes s).repr (planeCoordinates z-planeCoordinates c) 1| ≤ _
  rw [slopeAxes_repr_zero, slopeAxes_repr_one]
  change |((z.1-c.1)+s*(z.2-c.2))/Real.sqrt (1+s^2)| ≤ _ ∧
    |((z.2-c.2)-s*(z.1-c.1))/Real.sqrt (1+s^2)| ≤ _
  constructor
  · rw [heq]
    calc
      _ ≤ |Real.sqrt (1+s^2)*(z.1-c.1)|+
          |(s/Real.sqrt (1+s^2))*((z.2-c.2)-s*(z.1-c.1))| := abs_add_le _ _
      _ = Real.sqrt (1+s^2)*|z.1-c.1|+
          (|s|/Real.sqrt (1+s^2))*|(z.2-c.2)-s*(z.1-c.1)| := by
        rw [abs_mul, abs_mul, abs_div, abs_of_pos hqpos]
      _ ≤ Real.sqrt (1+s^2)*(a/2)+(|s|/Real.sqrt (1+s^2))*(b/2) :=
        add_le_add (mul_le_mul_of_nonneg_left hx hqpos.le)
          (mul_le_mul_of_nonneg_left hy (by positivity))
      _ = _ := by dsimp [slopeRectangle]; ring
  · rw [abs_div, abs_of_pos hqpos]
    exact (div_le_div_of_nonneg_right hy hqpos.le).trans_eq (by dsimp [slopeRectangle]; ring)

theorem slope_rectangle_area_le (s a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    (slopeRectangle (0,0) s a b ha hb hba).long *
      (slopeRectangle (0,0) s a b ha hb hba).short ≤ 2*a*b := by
  have hq : 0 < Real.sqrt (1+s^2) := Real.sqrt_pos.mpr (by positivity)
  have hq2 := Real.sq_sqrt (by positivity : 0 ≤ 1+s^2)
  have heq : (Real.sqrt (1+s^2)*a+|s|/Real.sqrt (1+s^2)*b)*
      (b/Real.sqrt (1+s^2)) = a*b+(|s|/(1+s^2))*b^2 := by
    field_simp
    rw [hq2]
  change (Real.sqrt (1+s^2)*a+|s|/Real.sqrt (1+s^2)*b)*
    (b/Real.sqrt (1+s^2)) ≤ _
  rw [heq]
  have habs : |s| ≤ 1+s^2 := by
    nlinarith [sq_nonneg (|s|-(1/2:ℝ)), sq_abs s]
  have hratio : |s|/(1+s^2) ≤ 1 :=
    (div_le_one (by positivity : 0 < 1+s^2)).mpr habs
  have hm := mul_le_mul_of_nonneg_right hratio (sq_nonneg b)
  have hb2 := mul_le_mul_of_nonneg_right hba hb.le
  nlinarith

theorem slope_rectangle_long_le (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hs : |s| ≤ 1) :
    (slopeRectangle c s a b ha hb hba).long ≤ 3*a := by
  have hq : 1 ≤ Real.sqrt (1+s^2) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg s])
  have hq2 := Real.sq_sqrt (by positivity : 0 ≤ 1+s^2)
  have hu : Real.sqrt (1+s^2) ≤ 2 := by
    nlinarith [sq_abs s, abs_nonneg s]
  have hr : |s|/Real.sqrt (1+s^2) ≤ 1 :=
    (div_le_one (by linarith : 0 < Real.sqrt (1+s^2))).mpr (hs.trans hq)
  change Real.sqrt (1+s^2)*a+|s|/Real.sqrt (1+s^2)*b ≤ _
  have h1 := mul_le_mul_of_nonneg_right hu ha.le
  have h2 := mul_le_mul_of_nonneg_right hr hb.le
  nlinarith

theorem slope_rectangle_short_ge (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hs : |s| ≤ 1) :
    b/2 ≤ (slopeRectangle c s a b ha hb hba).short := by
  have hqpos : 0 < Real.sqrt (1+s^2) := Real.sqrt_pos.mpr (by positivity)
  have hq2 := Real.sq_sqrt (by positivity : 0 ≤ 1+s^2)
  have hu : Real.sqrt (1+s^2) ≤ 2 := by
    nlinarith [sq_abs s, abs_nonneg s]
  change b/2 ≤ b/Real.sqrt (1+s^2)
  apply (le_div_iff₀ hqpos).mpr
  nlinarith

theorem slope_rectangle_aperture_ge (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hs : |s| ≤ 1) :
    b/(12*a) ≤ (slopeRectangle c s a b ha hb hba).short /
      (2*(slopeRectangle c s a b ha hb hba).long) := by
  let R := slopeRectangle c s a b ha hb hba
  have hlpos : 0 < R.long := R.short_pos.trans_le R.short_le_long
  have hlong : R.long ≤ 3*a := slope_rectangle_long_le c s a b ha hb hba hs
  have hshort : b/2 ≤ R.short := slope_rectangle_short_ge c s a b ha hb hba hs
  apply (div_le_div_iff₀ (by positivity : 0 < 12*a) (mul_pos (by norm_num) hlpos)).mpr
  have h1 := mul_le_mul_of_nonneg_left hlong hb.le
  have h2 := mul_le_mul_of_nonneg_left hshort ha.le
  nlinarith

theorem volume_slopeRectangle_le (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    volume (slopeRectangle c s a b ha hb hba).carrier ≤ ENNReal.ofReal (2*a*b) := by
  let R := slopeRectangle c s a b ha hb hba
  have hlong : 0 ≤ R.long := (R.short_pos.trans_le R.short_le_long).le
  rw [Rectangle.volume_carrier, ← ENNReal.ofReal_mul hlong]
  exact ENNReal.ofReal_le_ofReal (slope_rectangle_area_le s a b ha hb hba)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ClippedSlopeBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal clipping before Euclidean enclosure. The width of the
clipped interval is bounded by both the testing strip and the original
dilation; no large horizontal dilation enters the long-side restriction. -/

noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert.SlopeBox

theorem clipLength_le_strip (T : SlopeBox) (D l r : ℝ) : T.clipLength D l r ≤ r-l := by
  unfold clipLength clipLeft clipRight
  linarith [min_le_left r (T.x+D*T.length), le_max_left l (T.x-D*T.length)]

theorem clipLength_le_dilation (T : SlopeBox) (D l r : ℝ) :
    T.clipLength D l r ≤ 2*D*T.length := by
  unfold clipLength clipLeft clipRight
  linarith [min_le_right r (T.x+D*T.length), le_max_right l (T.x-D*T.length)]

theorem clipped_coordinates (T : SlopeBox) (D l r : ℝ) (z : ℝ × ℝ)
    (hx : z.1 ∈ Icc l r) (hz : z ∈ T.radialDilation D) :
    |z.1-(T.clipCenter D l r).1| ≤ T.clipLength D l r/2 ∧
      |(z.2-(T.clipCenter D l r).2)-T.slope*(z.1-(T.clipCenter D l r).1)| ≤ D*T.width := by
  have hrad : |T.horizontal z|+|T.transverse z| ≤ D := hz
  have hx0 : |z.1-T.x| ≤ D*T.length := by
    have hb : |T.horizontal z| ≤ D := by linarith [abs_nonneg (T.transverse z)]
    rw [horizontal, abs_div, abs_of_pos T.length_pos] at hb
    exact (div_le_iff₀ T.length_pos).mp hb
  have hy0 : |(z.2-T.y)-T.slope*(z.1-T.x)| ≤ D*T.width := by
    have hb : |T.transverse z| ≤ D := by linarith [abs_nonneg (T.horizontal z)]
    rw [transverse, abs_div, abs_of_pos T.width_pos] at hb
    exact (div_le_iff₀ T.width_pos).mp hb
  have hleft : T.clipLeft D l ≤ z.1 := max_le hx.1 (by linarith [(abs_le.mp hx0).1])
  have hright : z.1 ≤ T.clipRight D r := le_min hx.2 (by linarith [(abs_le.mp hx0).2])
  constructor
  · dsimp [clipCenter, clipLength]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · convert hy0 using 2
    all_goals try with_reducible_and_instances rfl
    dsimp [clipCenter]
    ring

theorem clipLength_pos_of_positive_witness (T : SlopeBox) (D l r : ℝ)
    (E : Set (ℝ × ℝ)) (hpos : 0 < (volume.prod volume) E)
    (hE : ∀ z ∈ E, z.1 ∈ Icc l r ∧ z ∈ T.radialDilation D) :
    0 < T.clipLength D l r := by
  by_contra h
  have hlen : T.clipLength D l r ≤ 0 := le_of_not_gt h
  have hsub : E ⊆ {(T.clipCenter D l r).1} ×ˢ (univ : Set ℝ) := by
    intro z hz
    have hc := (T.clipped_coordinates D l r z (hE z hz).1 (hE z hz).2).1
    have heq : z.1 = (T.clipCenter D l r).1 := by
      have : |z.1-(T.clipCenter D l r).1| = 0 := by
        exact le_antisymm (by linarith) (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp this)
    exact ⟨heq,mem_univ _⟩
  have hnull : (volume.prod volume) ({(T.clipCenter D l r).1} ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.prod_prod]
    simp
  have hzero := (measure_mono hsub).trans_eq hnull
  exact (not_lt_of_ge hzero) hpos

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TestingWeakTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover a weak-L2 distribution bound from the restricted L1 testing
inequality. Integrability supplies finiteness of the testing level set. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem weak_two_of_testing {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (hfi : Integrable f μ)
    (A : ℝ) (hA : 0 ≤ A)
    (htest : ∀ Q : Set Ω, MeasurableSet Q → μ Q ≠ ∞ →
      (∫⁻ x in Q, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal (A*Real.sqrt (μ.real Q)))
    (t : ℝ) (ht : 0 < t) :
    μ {x | t < f x} ≤ ENNReal.ofReal (A^2/t^2) := by
  let Q := {x | t < f x}
  have hQ : MeasurableSet Q := measurableSet_lt measurable_const hf
  have hfin : μ Q ≠ ∞ := (hfi.measure_gt_lt_top ht).ne
  have hlo : ENNReal.ofReal t * μ Q ≤ ∫⁻ x in Q, ENNReal.ofReal (f x) ∂μ := by
    calc
      _ = ∫⁻ _x in Q, ENNReal.ofReal t ∂μ := by simp
      _ ≤ _ := setLIntegral_mono' hQ (fun _ hx => ENNReal.ofReal_le_ofReal hx.le)
  have hle := hlo.trans (htest Q hQ hfin)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le,
    ENNReal.toReal_ofReal (mul_nonneg hA (Real.sqrt_nonneg _))] at hr
  change t * μ.real Q ≤ A * Real.sqrt (μ.real Q) at hr
  have hm : 0 ≤ μ.real Q := measureReal_nonneg
  have hs : t*Real.sqrt (μ.real Q) ≤ A := by
    by_cases hz : μ.real Q = 0
    · simpa [hz] using hA
    · have hx : 0 < Real.sqrt (μ.real Q) := Real.sqrt_pos.mpr (lt_of_le_of_ne hm (Ne.symm hz))
      apply (mul_le_mul_iff_right₀ hx).mp
      nlinarith [Real.sq_sqrt hm]
  have hs2 : t^2*μ.real Q ≤ A^2 := by
    have hsq := mul_self_le_mul_self (by positivity : 0 ≤ t*Real.sqrt (μ.real Q)) hs
    nlinarith [Real.sq_sqrt hm]
  have hreal : μ.real Q ≤ A^2/t^2 := (le_div_iff₀ (sq_pos_of_pos ht)).mpr (by nlinarith)
  change μ Q ≤ _
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hreal

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopDilatedTesting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the dilation costs in the popular-top testing estimate.
The exponent three comes from the two-dimensional dilation and the
weak-L2 layer-cake estimate; degree four already makes the series summable. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert

theorem dyadic_cubic_decay (D R A : ℝ) (hD : 4 ≤ D) (hR : 0 ≤ R) (hA : 0 ≤ A) (n : ℕ) :
    (4^D*(2^(-D))^n)*(A*(R*2^n)^3) ≤ (4^D*A*R^3)*((1:ℝ)/2)^n := by
  have hq : (2:ℝ)^(-D)*8 ≤ (1:ℝ)/2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show -D ≤ (-4:ℝ) by linarith)
    norm_num at h
    linarith
  have heq : (4^D*(2^(-D))^n)*(A*(R*2^n)^3) =
      (4^D*A*R^3)*((2:ℝ)^(-D)*8)^n := by
    rw [mul_pow, mul_pow, show ((2:ℝ)^n)^3 = (8:ℝ)^n by rw [← pow_mul, mul_comm n, pow_mul]; norm_num]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq n) (by positivity)

theorem top_lintegral_of_dilated_testing {ι : Type*} [Fintype ι]
    (μ : Measure (ℝ × ℝ)) (T : ι → SlopeBox) (K R D A : ℝ)
    (hK : 0 < K) (hKR : K ≤ R) (hD : 4 ≤ D) (hA : 0 ≤ A)
    (htest : ∀ n : ℕ, (∑ i, μ ((T i).radialDilation (R*2^n))) ≤
      ENNReal.ofReal (A*(R*2^n)^3)) :
    (∫⁻ z, ENNReal.ofReal (∑ i, (T i).weight K D z) ∂μ) ≤
      ENNReal.ofReal (2*4^D*A*R^3) := by
  classical
  have hD0 : 0 ≤ D := by linarith
  have hR : 0 ≤ R := (hK.trans_le hKR).le
  have hweight (i : ι) :
      (∫⁻ z, ENNReal.ofReal ((T i).weight K D z) ∂μ) ≤
        ∑' n : ℕ, ENNReal.ofReal (4^D*(2^(-D))^n) *
          μ ((T i).radialDilation (R*2^n)) := by
    calc
      _ ≤ ∫⁻ z, ∑' n : ℕ, ENNReal.ofReal (4^D*(2^(-D))^n) *
          ((T i).radialDilation (R*2^n)).indicator (fun _ => (1:ℝ≥0∞)) z ∂μ :=
        lintegral_mono ((T i).weight_le_dyadic_sum K R D hK hKR hD0)
      _ = _ := by
        rw [lintegral_tsum]
        · congr 1; funext n
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_indicator_fun_one ((T i).measurableSet_radialDilation _)]
        · intro n
          exact (measurable_const.mul (measurable_const.indicator
            ((T i).measurableSet_radialDilation _))).aemeasurable
  calc
    _ = ∑ i, ∫⁻ z, ENNReal.ofReal ((T i).weight K D z) ∂μ := by
      simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ((T i).weight_pos hK D _).le)]
      exact lintegral_finsetSum _ (fun i _ =>
        ((T i).weight_continuous K D hK).measurable.ennreal_ofReal)
    _ ≤ ∑ i, ∑' n : ℕ, ENNReal.ofReal (4^D*(2^(-D))^n) *
        μ ((T i).radialDilation (R*2^n)) := Finset.sum_le_sum fun i _ => hweight i
    _ = ∑' n : ℕ, ENNReal.ofReal (4^D*(2^(-D))^n) *
        ∑ i, μ ((T i).radialDilation (R*2^n)) := by
      rw [← tsum_fintype (L := SummationFilter.unconditional _), ENNReal.tsum_comm]
      simp only [tsum_fintype, Finset.mul_sum]
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((4^D*A*R^3)*((1:ℝ)/2)^n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      calc
        _ ≤ ENNReal.ofReal (4^D*(2^(-D))^n)*ENNReal.ofReal (A*(R*2^n)^3) :=
          mul_le_mul' le_rfl (htest n)
        _ = ENNReal.ofReal ((4^D*(2^(-D))^n)*(A*(R*2^n)^3)) := by
          exact (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (dyadic_cubic_decay D R A hD hR hA n)
    _ = ENNReal.ofReal (2*4^D*A*R^3) := by
      have hs : Summable (fun n : ℕ => ((1:ℝ)/2)^n) :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hs.mul_left _),
        tsum_mul_left, tsum_geometric_two]
      congr 1
      ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RestrictedTopWeakTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricted testing gives the top-count bound on the localization
strip, without extending the short-side geometry beyond that strip. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

theorem top_count_weak_two_on_set {ι : Type*} [Fintype ι]
    (T : ι → SlopeBox) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (K R D A : ℝ) (hK : 0 < K) (hKR : K ≤ R) (hD : 4 ≤ D) (hA : 0 ≤ A)
    (htest : ∀ Q : Set (ℝ × ℝ), MeasurableSet Q →
      (volume.prod volume) Q ≠ ∞ → Q ⊆ S → ∀ n : ℕ,
      (∑ i, (volume.prod volume) (Q ∩ (T i).radialDilation (R*2^n))) ≤
        ENNReal.ofReal (A*(R*2^n)^3*Real.sqrt ((volume.prod volume).real Q)))
    (t : ℝ) (ht : 0 < t) :
    (volume.prod volume) (S ∩ {z | t < ∑ i, (T i).weight K D z}) ≤
      ENNReal.ofReal ((2*4^D*A*R^3)^2/t^2) := by
  classical
  let μ := (volume.prod volume).restrict S
  have hm : Measurable (fun z => ∑ i, (T i).weight K D z) :=
    Finset.measurable_sum _ (fun i _ => ((T i).weight_continuous K D hK).measurable)
  have hi : Integrable (fun z => ∑ i, (T i).weight K D z) μ :=
    (integrable_finsetSum _ (fun i _ => (T i).weight_integrable hK (by linarith))).mono_measure
      Measure.restrict_le_self
  have hw := weak_two_of_testing μ _ hm hi (2*4^D*A*R^3)
    (by have : 0 < R := hK.trans_le hKR; positivity) (by
      intro Q hQ hQfin
      have hQfin' : (volume.prod volume) (Q ∩ S) ≠ ∞ := by
        simpa only [μ, Measure.restrict_apply hQ] using hQfin
      have hQS : μ.real Q = (volume.prod volume).real (Q ∩ S) := by
        simp only [Measure.real, μ, Measure.restrict_apply hQ]
      have hd := top_lintegral_of_dilated_testing (μ.restrict Q) T K R D
        (A*Real.sqrt (μ.real Q)) hK hKR hD (by positivity) (by
          intro n
          have hp := htest (Q ∩ S) (hQ.inter hS) hQfin' inter_subset_right n
          simpa only [μ, Measure.restrict_apply ((T _).measurableSet_radialDilation _),
            Measure.restrict_apply (((T _).measurableSet_radialDilation _).inter hQ),
            Measure.restrict_apply (hQ.inter ((T _).measurableSet_radialDilation _)),
            hQS, inter_assoc, inter_comm, inter_left_comm, mul_assoc, mul_comm, mul_left_comm]
            using hp)
      convert hd using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring) t ht
  simpa only [μ, Measure.restrict_apply (measurableSet_lt measurable_const hm), inter_comm]
    using hw

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeakTwoIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restricted L1 estimate needed for mask removal, derived from
an actual weak (2,2) distribution estimate by layer cake. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem lintegral_inverse_square_tail (K t : ℝ) (ht : 0 < t) :
    (∫⁻ s in Ioi t, ENNReal.ofReal (K^2/s^2)) = ENNReal.ofReal (K^2/t) := by
  have hpow (s : ℝ) : s^(-2:ℝ) = (s^2)⁻¹ := by
    rw [Real.rpow_neg_ofNat]
    simp
  have hfun : (fun s : ℝ => K^2/s^2) = fun s => K^2*s^(-2:ℝ) := by
    funext s
    rw [hpow, div_eq_mul_inv]
  have hi : IntegrableOn (fun s : ℝ => K^2/s^2) (Ioi t) volume := by
    rw [hfun]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) ht).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun s => div_nonneg (sq_nonneg K) (sq_nonneg s)))]
  rw [hfun, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) ht]
  norm_num [Real.rpow_neg_one, div_eq_mul_inv]

theorem weak_two_lintegral_split {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : AEMeasurable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (K t : ℝ) (ht : 0 < t)
    (hweak : ∀ s : ℝ, 0 < s → μ {x | s < f x} ≤ ENNReal.ofReal (K^2/s^2)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal t*μ univ+ENNReal.ofReal (K^2/t) := by
  rw [lintegral_eq_lintegral_meas_lt μ hf0 hf,
    ← Ioc_union_Ioi_eq_Ioi ht.le]
  calc
    _ ≤ (∫⁻ s in Ioc 0 t, μ {x | s < f x}) +
        ∫⁻ s in Ioi t, μ {x | s < f x} := lintegral_union_le _ _ _
    _ ≤ (∫⁻ _s in Ioc 0 t, μ univ) + ∫⁻ s in Ioi t, ENNReal.ofReal (K^2/s^2) := by
      apply add_le_add
      · exact lintegral_mono (fun _ => measure_mono (subset_univ _))
      · exact setLIntegral_mono' measurableSet_Ioi (fun s hs => hweak s (ht.trans hs))
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
        lintegral_inverse_square_tail K t ht, mul_comm (μ univ)]

theorem weak_two_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : μ univ ≠ 0)
    (f : Ω → ℝ) (hf : AEMeasurable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (K : ℝ) (hK : 0 < K)
    (hweak : ∀ s : ℝ, 0 < s → μ {x | s < f x} ≤ ENNReal.ofReal (K^2/s^2)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤
      ENNReal.ofReal (2*K*Real.sqrt ((μ univ).toReal)) := by
  let M := (μ univ).toReal
  have hM : 0 < M := ENNReal.toReal_pos hμ (measure_ne_top μ univ)
  have hS : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  have ht : 0 < K/Real.sqrt M := div_pos hK hS
  have hm : μ univ = ENNReal.ofReal M := (ENNReal.ofReal_toReal (measure_ne_top μ univ)).symm
  have h := weak_two_lintegral_split μ f hf hf0 K (K/Real.sqrt M) ht hweak
  rw [hm, ← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_add (by positivity) (by positivity)] at h
  have heq : K/Real.sqrt M*M+K^2/(K/Real.sqrt M) = 2*K*Real.sqrt M := by
    field_simp
    nlinarith [Real.sq_sqrt hM.le]
  exact h.trans_eq (congrArg ENNReal.ofReal heq)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedDilationLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact weighted layer-cake step for a finite family of dilated
rectangles. Its measure is the sum of the top areas, not a counting measure. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert

theorem weighted_layer_from_weak_tail {ι : Type*} [Fintype ι] (w : ι → ℝ≥0) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (K : ℝ) (hK : 0 < K)
    (hS : 0 < ∑ i, (w i : ℝ))
    (htail : ∀ t : ℝ, 0 < t →
      (∑ i, if t < a i then (w i : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (K^2/t^2)) :
    (∑ i, (w i : ℝ≥0∞)*ENNReal.ofReal (a i)) ≤
      ENNReal.ofReal (2*K*Real.sqrt (∑ i, (w i : ℝ))) := by
  classical
  let : MeasurableSpace ι := ⊤
  let μ : Measure ι := ∑ i, w i • Measure.dirac i
  have hμset (s : Set ι) : μ s = ∑ i, if i ∈ s then (w i : ℝ≥0∞) else 0 := by
    simp only [μ, Measure.finsetSum_apply, Measure.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ s <;> simp [hi, ENNReal.smul_def]
  have hμuniv : μ univ = ∑ i, (w i : ℝ≥0∞) := by simp [hμset]
  have hmass : (μ univ).toReal = ∑ i, (w i : ℝ) := by
    rw [hμuniv, ENNReal.toReal_sum]
    · simp
    · intro i _; exact ENNReal.coe_ne_top
  have : IsFiniteMeasure μ := by
    constructor
    rw [hμuniv]
    exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.coe_lt_top)
  have hnonzero : μ univ ≠ 0 := by
    intro h
    rw [h, ENNReal.toReal_zero] at hmass
    linarith
  have h := weak_two_lintegral μ hnonzero a (measurable_of_countable a).aemeasurable
    (Filter.Eventually.of_forall ha) K hK (by
      intro t ht
      simpa only [hμset, mem_ofPred_eq] using htail t ht)
  rw [hmass] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  change (∑ i, (w i : ℝ≥0∞)*ENNReal.ofReal (a i)) =
    ∫⁻ x, ENNReal.ofReal (a x) ∂(∑ i, w i • Measure.dirac i)
  rw [lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_smul_measure, lintegral_dirac]
  simp only [ENNReal.smul_def, smul_eq_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SquareTailLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted layer-cake estimate in the product form produced by
the covering inequality. All weights are the actual top areas. -/

noncomputable section
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert

theorem weighted_layer_from_square_tail {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (K : ℝ) (hK : 0 < K) (hS : 0 < ∑ i, (w i : ℝ))
    (htail : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t^2)*(∑ i, if t<a i then (w i:ℝ≥0∞) else 0) ≤
        ENNReal.ofReal (K^2)) :
    (∑ i, (w i:ℝ≥0∞)*ENNReal.ofReal (a i)) ≤
      ENNReal.ofReal (2*K*Real.sqrt (∑ i, (w i:ℝ))) := by
  apply weighted_layer_from_weak_tail w a ha K hK hS
  intro t ht
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos ht)]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  simpa only [mul_comm] using htail t ht

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopAreaAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual normalized intersection averages and top-area weights. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert.SlopeBox

theorem dilationAverage_nonneg (T : SlopeBox) (D : ℝ) (Q : Set (ℝ × ℝ)) :
    0 ≤ T.dilationAverage D Q := by
  unfold dilationAverage
  have := T.length_pos
  have := T.width_pos
  positivity

theorem dilationAverage_normalized (T : SlopeBox) (D : ℝ) (hD : 0 < D)
    (Q : Set (ℝ × ℝ)) (hQfin : (volume.prod volume) Q ≠ ∞) :
    ENNReal.ofReal (T.dilationAverage D Q*(8*D^2*T.length*T.width)) =
      (volume.prod volume) (Q ∩ T.radialDilation D) := by
  have hB : 8*D^2*T.length*T.width ≠ 0 := by
    have := T.length_pos
    have := T.width_pos
    positivity
  have hi : (volume.prod volume) (Q ∩ T.radialDilation D) ≠ ∞ :=
    ne_top_of_le_ne_top hQfin (measure_mono inter_subset_left)
  rw [dilationAverage, div_mul_cancel₀ _ hB]
  exact ENNReal.ofReal_toReal hi

theorem dilation_intersection_eq (T : SlopeBox) (D : ℝ) (hD : 0 < D)
    (Q : Set (ℝ × ℝ)) (hQfin : (volume.prod volume) Q ≠ ∞) :
    (volume.prod volume) (Q ∩ T.radialDilation D) =
      ENNReal.ofReal (8*D^2)*((T.areaWeight:ℝ≥0∞)*ENNReal.ofReal (T.dilationAverage D Q)) := by
  rw [ennreal_areaWeight, ← ENNReal.ofReal_mul T.area_pos.le,
    ← ENNReal.ofReal_mul (by positivity), ← T.dilationAverage_normalized D hD Q hQfin]
  congr 1
  unfold area
  ring

theorem sum_dilation_intersection_eq {ι : Type*} [Fintype ι]
    (T : ι → SlopeBox) (D : ℝ) (hD : 0 < D)
    (Q : Set (ℝ × ℝ)) (hQfin : (volume.prod volume) Q ≠ ∞) :
    (∑ i, (volume.prod volume) (Q ∩ (T i).radialDilation D)) =
      ENNReal.ofReal (8*D^2)*∑ i, ((T i).areaWeight:ℝ≥0∞)*ENNReal.ofReal ((T i).dilationAverage D Q) := by
  simp only [dilation_intersection_eq _ D hD Q hQfin, Finset.mul_sum]

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectangleIndicator
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indicator tests in the precise normalization of the published
rectangle maximal estimate. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem squareIntegral_indicator (Q : Set Plane) (hQ : MeasurableSet Q) :
    squareIntegral volume (Q.indicator (fun _ => (1:ℝ))) = volume Q := by
  unfold squareIntegral
  have heq (x : Plane) : ‖Q.indicator (fun _ => (1:ℝ)) x‖ₑ^2 =
      Q.indicator (fun _ => (1:ℝ≥0∞)) x := by
    by_cases hx : x ∈ Q <;> simp [hx]
  simp_rw [heq]
  exact lintegral_indicator_fun_one hQ

namespace Rectangle

theorem average_indicator (R : Rectangle) (Q : Set Plane) (hQ : MeasurableSet Q) :
    R.average (Q.indicator (fun _ => (1:ℝ))) =
      (volume R.carrier)⁻¹ * volume (R.carrier ∩ Q) := by
  unfold average
  have heq (x : Plane) : ‖Q.indicator (fun _ => (1:ℝ)) x‖ₑ =
      Q.indicator (fun _ => (1:ℝ≥0∞)) x := by
    by_cases hx : x ∈ Q <;> simp [hx]
  simp_rw [heq]
  rw [lintegral_indicator_fun_one hQ, Measure.restrict_apply hQ, inter_comm]

theorem indicator_average_lower (R : Rectangle) (Q S : Set Plane) (hQ : MeasurableSet Q)
    (hsub : S ⊆ Q ∩ R.carrier) (B β : ℝ) (_hB : 0 < B) (hβ : 0 ≤ β)
    (harea : volume R.carrier ≤ ENNReal.ofReal B)
    (hintersection : ENNReal.ofReal (β*B) ≤ volume S) :
    ENNReal.ofReal β ≤ R.average (Q.indicator (fun _ => (1:ℝ))) := by
  rw [average_indicator R Q hQ]
  have hnum : ENNReal.ofReal β * volume R.carrier ≤ volume (R.carrier ∩ Q) := by
    calc
      _ ≤ ENNReal.ofReal β*ENNReal.ofReal B := mul_le_mul' le_rfl harea
      _ = ENNReal.ofReal (β*B) := (ENNReal.ofReal_mul hβ).symm
      _ ≤ volume S := hintersection
      _ ≤ _ := measure_mono (by simpa only [inter_comm] using hsub)
  have h := mul_le_mul' (le_refl ((volume R.carrier)⁻¹)) hnum
  simpa only [← mul_assoc, mul_left_comm ((volume R.carrier)⁻¹) (ENNReal.ofReal β),
    ENNReal.inv_mul_cancel R.volume_carrier_pos.ne' R.volume_carrier_ne_top, mul_one] using h

end Rectangle
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SlopeDirection
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative normalization of slope directions and the exact
uncertainty-arc condition needed by the Lacey--Li rectangle input. -/

noncomputable section
open scoped BigOperators NNReal
namespace LipschitzHilbert

theorem slopeDirection_norm (s : ℝ) : ‖slopeDirection s‖ = 1 :=
  (slopeAxes s).norm_eq_one 0

theorem slopeDirection_coordinates (s : ℝ) :
    slopeDirection s = WithLp.toLp 2 ![Real.cos (Real.arctan s), Real.sin (Real.arctan s)] := by
  rw [slopeDirection, slopeAxes_apply]
  simp [slopeAxisVectors, Real.cos_arctan, Real.sin_arctan]

theorem slopeDirection_inner (u s : ℝ) :
    inner ℝ (slopeDirection u) (slopeDirection s) = Real.cos (Real.arctan u-Real.arctan s) := by
  rw [slopeDirection_coordinates, slopeDirection_coordinates]
  change (∑ i : Fin 2, (![Real.cos (Real.arctan s), Real.sin (Real.arctan s)] i)*
    (![Real.cos (Real.arctan u), Real.sin (Real.arctan u)] i)) = _
  simp [Fin.sum_univ_two, Real.cos_sub]
  ring

theorem arctan_lipschitz : LipschitzWith 1 Real.arctan := by
  apply lipschitzWith_of_nnnorm_deriv_le Real.differentiable_arctan
  intro x
  rw [← NNReal.coe_le_coe]
  change ‖deriv Real.arctan x‖ ≤ (1:ℝ)
  rw [Real.deriv_arctan]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_one (by positivity : 0 < 1+x^2)).mpr (by nlinarith [sq_nonneg x])

theorem arctan_sub_le (u s : ℝ) : |Real.arctan u-Real.arctan s| ≤ |u-s| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using arctan_lipschitz.dist_le_mul u s

theorem slopeDirection_lipschitz : LipschitzWith 2 slopeDirection := by
  apply LipschitzWith.of_dist_le_mul
  intro u s
  rw [dist_eq_norm]
  have hc := Real.abs_cos_sub_cos_le (Real.arctan u) (Real.arctan s)
  have hs := Real.abs_sin_sub_sin_le (Real.arctan u) (Real.arctan s)
  have ha := arctan_sub_le u s
  have hn := plane_norm_le_coordinate_sum (slopeDirection u-slopeDirection s)
  rw [slopeDirection_coordinates, slopeDirection_coordinates] at hn
  change ‖slopeDirection u-slopeDirection s‖ ≤ (2:ℝ)*dist u s
  rw [slopeDirection_coordinates, slopeDirection_coordinates]
  simp only [PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hn
  rw [Real.dist_eq]
  linarith

theorem cos_le_inner_slopeDirection (u s θ : ℝ) (hθ : θ ≤ Real.pi)
    (hclose : |u-s| ≤ θ) :
    Real.cos θ ≤ inner ℝ (slopeDirection u) (slopeDirection s) := by
  rw [slopeDirection_inner, ← Real.cos_abs (Real.arctan u-Real.arctan s)]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hθ
    ((arctan_sub_le u s).trans hclose)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_VerticalRectangle
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical Euclidean enclosures of fat slope parallelograms. The
constant vertical field makes every such enclosure Lacey--Li admissible. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace LipschitzHilbert

theorem verticalAxes_repr_zero (z : Plane) : verticalAxes.repr z 0 = z 1 := by
  rw [OrthonormalBasis.repr_apply_apply, verticalAxes, OrthonormalBasis.reindex_apply]
  simp [slopeAxes_apply, slopeAxisVectors, PiLp.inner_apply, Fin.sum_univ_two]

theorem verticalAxes_repr_one (z : Plane) : verticalAxes.repr z 1 = z 0 := by
  rw [OrthonormalBasis.repr_apply_apply, verticalAxes, OrthonormalBasis.reindex_apply]
  simp [slopeAxes_apply, slopeAxisVectors, PiLp.inner_apply, Fin.sum_univ_two]

theorem mem_verticalRectangle (c z : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (hx : |z.1-c.1| ≤ a/2) (hy : |(z.2-c.2)-s*(z.1-c.1)| ≤ b/2) :
    planeCoordinates z ∈ (verticalRectangle c s a b ha hab).carrier := by
  change |verticalAxes.repr (planeCoordinates z-planeCoordinates c) 0| ≤ _ ∧
    |verticalAxes.repr (planeCoordinates z-planeCoordinates c) 1| ≤ _
  rw [verticalAxes_repr_zero,verticalAxes_repr_one]
  refine ⟨?_,hx⟩
  change |z.2-c.2| ≤ (b+|s| * a)/2
  calc
    _ = |((z.2-c.2)-s*(z.1-c.1))+s*(z.1-c.1)| := by congr 1; ring
    _ ≤ |(z.2-c.2)-s*(z.1-c.1)|+|s*(z.1-c.1)| := abs_add_le _ _
    _ ≤ b/2+|s| * (a/2) := add_le_add hy (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg s))
    _ = _ := by ring

theorem volume_verticalRectangle_le (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hs : |s| ≤ 1) :
    volume (verticalRectangle c s a b ha hab).carrier ≤ ENNReal.ofReal (2*a*b) := by
  rw [Rectangle.volume_carrier, ← ENNReal.ofReal_mul (by
    change 0 ≤ b+|s| * a; have hb := ha.trans_le hab; positivity)]
  apply ENNReal.ofReal_le_ofReal
  change (b+|s| * a)*a ≤ _
  have h1 := mul_le_mul_of_nonneg_right hs ha.le
  have h2 := mul_le_mul_of_nonneg_right hab ha.le
  have h3 := mul_le_mul_of_nonneg_right h1 ha.le
  nlinarith

theorem constant_axis_popular (R : Rectangle) :
    R.popularSet (fun _ => R.axes 0) = R.carrier := by
  ext z
  simp only [Rectangle.popularSet, mem_ofPred_eq]
  rw [real_inner_self_eq_norm_sq, R.axes.norm_eq_one, one_pow]
  exact and_iff_left (Real.cos_le_one _)

theorem constant_axis_admissible (R : Rectangle) (δ : ℝ≥0) (hδ : δ ≤ 1) :
    R.Admissible (fun _ => R.axes 0) 0 δ := by
  constructor
  · simp
  · rw [constant_axis_popular]
    exact mul_le_of_le_one_left' (by exact_mod_cast hδ)

theorem verticalRectangle_admissible (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    (verticalRectangle c s a b ha hab).Admissible (fun _ => verticalAxes 0) 0 (1/2) :=
  constant_axis_admissible _ _ (by norm_num)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FatEnclosure
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fat clipped tops have vertical enclosing rectangles. Lacey--Li for
the constant vertical field handles them without a length restriction. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace LipschitzHilbert.SlopeBox

theorem mem_fatEnclosure (T : SlopeBox) (D l r : ℝ)
    (ha : 0 < T.clipLength D l r) (hfat : T.clipLength D l r ≤ 2*D*T.width)
    (z : ℝ × ℝ) (hx : z.1 ∈ Icc l r) (hz : z ∈ T.radialDilation D) :
    planeCoordinates z ∈ (T.fatEnclosure D l r ha hfat).carrier := by
  obtain ⟨h1,h2⟩ := T.clipped_coordinates D l r z hx hz
  apply mem_verticalRectangle _ _ _ _ _ _ _ h1
  simpa only [show 2*D*T.width/2 = D*T.width by ring] using h2

theorem fatEnclosure_volume_le (T : SlopeBox) (D l r : ℝ) (hD : 0 < D)
    (ha : 0 < T.clipLength D l r) (hfat : T.clipLength D l r ≤ 2*D*T.width)
    (hs : |T.slope| ≤ 1) :
    volume (T.fatEnclosure D l r ha hfat).carrier ≤
      ENNReal.ofReal (8*D^2*T.length*T.width) := by
  apply (volume_verticalRectangle_le _ _ _ _ _ _ hs).trans
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_right (T.clipLength_le_dilation D l r)
    (show 0 ≤ 4*D*T.width by have := T.width_pos; positivity)
  nlinarith

theorem fatEnclosure_admissible (T : SlopeBox) (D l r : ℝ)
    (ha : 0 < T.clipLength D l r) (hfat : T.clipLength D l r ≤ 2*D*T.width) :
    (T.fatEnclosure D l r ha hfat).Admissible (fun _ => verticalAxes 0) 0 (1/2) :=
  verticalRectangle_admissible _ _ _ _ _ _

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_LaceyLiPacking
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted distribution bounds for disjoint popularity witnesses,
derived directly from the cited finite-rectangle Lacey--Li input. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert

theorem laceyLi_weighted_tail (hLL : LaceyLiInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (v : Plane → Plane) (K δ : ℝ≥0),
      LipschitzWith K v → (∀ x, ‖v x‖ = 1) → 0 < δ → δ < 1 →
      ∀ (n : ℕ) (R : Fin n → Rectangle), (∀ i, (R i).Admissible v K δ) →
      ∀ (E : Fin n → Set Plane) (w : Fin n → ℝ≥0∞) (α : ℝ≥0∞),
      (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i, E i ⊆ (R i).carrier) → (∀ i, α*w i ≤ volume (E i)) →
      ∀ (h : Plane → ℝ), MemLp h 2 volume →
      ∀ (a : Fin n → ℝ), (∀ i, ENNReal.ofReal (a i) ≤ (R i).average h) →
      ∀ t : ℝ≥0, 0 < t →
        (t : ℝ≥0∞)^2*α*(∑ i, if (t:ℝ) < a i then w i else 0) ≤
          (C : ℝ≥0∞)^2/(δ:ℝ≥0∞)*squareIntegral volume h := by
  classical
  obtain ⟨C,hC,hbound⟩ := hLL
  refine ⟨C,hC,?_⟩
  intro v K δ hv hu hδ hδ1 n R hR E w α hE hdisj hsub hsize h hh a ha t ht
  let F : Fin n → Set Plane := fun i => if (t:ℝ) < a i then E i else ∅
  let level : Set Plane := {x | (t:ℝ≥0∞) < rectangleMaximum R h x}
  have hFmeas : ∀ i, MeasurableSet (F i) := by
    intro i; dsimp [F]; split_ifs <;> simp_all
  have hFsub (i : Fin n) : F i ⊆ E i := by
    dsimp [F]; split_ifs <;> simp
  have hFd : Pairwise fun i j => Disjoint (F i) (F j) := by
    intro i j hij
    exact (hdisj hij).mono (hFsub i) (hFsub j)
  have hlevel (i : Fin n) : F i ⊆ level := by
    intro x hx
    by_cases hi : (t:ℝ) < a i
    · have hEi : x ∈ E i := hFsub i hx
      have hmx : (R i).average h ≤ rectangleMaximum R h x := by
        simpa only [rectangleMaximum, ite_eq_left (hsub i hEi)] using
          (Finset.le_sup (f := fun j => if x ∈ (R j).carrier then (R j).average h else 0)
            (Finset.mem_univ i))
      have ht' : (t:ℝ≥0∞) < ENNReal.ofReal (a i) := by
        have htR : (0:ℝ) < t := by exact_mod_cast ht
        simpa only [ENNReal.ofReal_coe_nnreal] using
          (ENNReal.ofReal_lt_ofReal_iff (htR.trans hi)).mpr hi
      exact ht'.trans_le ((ha i).trans hmx)
    · simp [F, hi] at hx
  have hpack := disjoint_witness_packing volume F (fun _ => level)
    (fun i => if (t:ℝ) < a i then w i else 0) α hFmeas hFd hlevel (by
      intro i; dsimp [F]; split_ifs with hi
      · exact hsize i
      · simp)
  have hp : α*(∑ i, if (t:ℝ) < a i then w i else 0) ≤ volume level :=
    hpack.trans (measure_mono (iUnion_subset (fun _ => Subset.rfl)))
  calc
    _ = (t:ℝ≥0∞)^2*(α*(∑ i, if (t:ℝ) < a i then w i else 0)) := by ring
    _ ≤ (t:ℝ≥0∞)^2*volume level := mul_le_mul' le_rfl hp
    _ ≤ _ := hbound v K δ hv hu hδ hδ1 n R hR h hh t ht

theorem laceyLi_weighted_tail_fintype (hLL : LaceyLiInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (v : Plane → Plane) (K δ : ℝ≥0),
      LipschitzWith K v → (∀ x, ‖v x‖ = 1) → 0 < δ → δ < 1 →
      ∀ (ι : Type*) [Fintype ι] (R : ι → Rectangle), (∀ i, (R i).Admissible v K δ) →
      ∀ (E : ι → Set Plane) (w : ι → ℝ≥0∞) (α : ℝ≥0∞),
      (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i, E i ⊆ (R i).carrier) → (∀ i, α*w i ≤ volume (E i)) →
      ∀ (h : Plane → ℝ), MemLp h 2 volume →
      ∀ (a : ι → ℝ), (∀ i, ENNReal.ofReal (a i) ≤ (R i).average h) →
      ∀ t : ℝ≥0, 0 < t →
        (t : ℝ≥0∞)^2*α*(∑ i, if (t:ℝ) < a i then w i else 0) ≤
          (C : ℝ≥0∞)^2/(δ:ℝ≥0∞)*squareIntegral volume h := by
  classical
  obtain ⟨C,hC,hbound⟩ := laceyLi_weighted_tail hLL
  refine ⟨C,hC,?_⟩
  intro v K δ hv hu hδ hδ1 ι _ R hR E w α hE hdisj hsub hsize h hh a ha t ht
  let e := (Fintype.equivFin ι).symm
  have h := hbound v K δ hv hu hδ hδ1 (Fintype.card ι) (R ∘ e)
    (fun i => hR (e i)) (E ∘ e) (w ∘ e) α (fun i => hE (e i))
    (fun i j hij => hdisj (fun heq => hij (e.injective heq)))
    (fun i => hsub (e i)) (fun i => hsize (e i)) h hh (a ∘ e) (fun i => ha (e i)) t ht
  simpa only [Function.comp_apply, e.sum_comp (fun i => if (t:ℝ) < a i then w i else 0)] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FatTopTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted tails for actual fat tops. The same published input suffices:
the vertical enclosing rectangles are fully popular for a constant field. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace LipschitzHilbert

theorem fat_top_weighted_tail (hLL : LaceyLiInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox) (D l r : ℝ),
      0 < D → (∀ i, 0 < (T i).clipLength D l r) →
      (∀ i, (T i).clipLength D l r ≤ 2*D*(T i).width) →
      (∀ i, |(T i).slope| ≤ 1) →
      ∀ (E : ι → Set (ℝ × ℝ)) (w : ι → ℝ≥0∞) (α : ℝ≥0∞),
      (∀ i, MeasurableSet (E i)) → (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation D) →
      (∀ i, α*w i ≤ (volume.prod volume) (E i)) →
      ∀ Q : Set (ℝ × ℝ), MeasurableSet Q → (volume.prod volume) Q ≠ ∞ →
      (∀ z ∈ Q, z.1 ∈ Icc l r) → ∀ a : ι → ℝ,
      (∀ i, 0 ≤ a i) →
      (∀ i, ENNReal.ofReal (a i*(8*D^2*(T i).length*(T i).width)) ≤
        (volume.prod volume) (Q ∩ (T i).radialDilation D)) →
      ∀ t : ℝ≥0, 0 < t →
      (t:ℝ≥0∞)^2*α*(∑ i, if (t:ℝ)<a i then w i else 0) ≤
        (C:ℝ≥0∞)^2/(1/2:ℝ≥0∞)*(volume.prod volume) Q := by
  classical
  obtain ⟨C,hC,hbound⟩ := laceyLi_weighted_tail_fintype hLL
  refine ⟨C,hC,?_⟩
  intro ι _ T D l r hD ha hfat hs E w α hEmeas hdisj hE hsize
    Q hQ hQfin hstrip a ha0 havg t ht
  let R : ι → Rectangle := fun i => (T i).fatEnclosure D l r (ha i) (hfat i)
  let E' : ι → Set Plane := fun i => planeCoordinates '' E i
  let Q' : Set Plane := planeCoordinates '' Q
  have hQ' : MeasurableSet Q' := planeCoordinates.measurableSet_image.mpr hQ
  have hQfin' : volume Q' ≠ ∞ := by simpa [Q',planeCoordinates_image_measure] using hQfin
  have hdisj' : Pairwise fun i j => Disjoint (E' i) (E' j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have hxy : x = y := planeCoordinates.injective (hxz.trans hyz.symm)
    subst y
    exact disjoint_left.mp (hdisj hij) hx hy
  have havg' (i : ι) : ENNReal.ofReal (a i) ≤ (R i).average (Q'.indicator (fun _ => (1:ℝ))) := by
    have hinter : ENNReal.ofReal (a i*(8*D^2*(T i).length*(T i).width)) ≤
        volume (planeCoordinates '' (Q ∩ (T i).radialDilation D)) := by
      simpa only [planeCoordinates_image_measure] using havg i
    apply Rectangle.indicator_average_lower (R i) Q'
      (planeCoordinates '' (Q ∩ (T i).radialDilation D)) hQ' _
      (8*D^2*(T i).length*(T i).width) (a i)
      (by have := (T i).length_pos; have := (T i).width_pos; positivity) (ha0 i)
      ((T i).fatEnclosure_volume_le D l r hD (ha i) (hfat i) (hs i)) hinter
    rintro z ⟨x,⟨hxQ,hxD⟩,rfl⟩
    exact ⟨mem_image_of_mem _ hxQ,(T i).mem_fatEnclosure D l r (ha i) (hfat i) x
      (hstrip x hxQ) hxD⟩
  have h := hbound (fun _ => verticalAxes 0) 0 (1/2) (LipschitzWith.const _)
    (fun _ => verticalAxes.norm_eq_one 0) (by norm_num) (by norm_num) ι R
    (fun i => (T i).fatEnclosure_admissible D l r (ha i) (hfat i)) E' w α
    (fun i => planeCoordinates.measurableSet_image.mpr (hEmeas i)) hdisj'
    (by
      intro i z hz
      obtain ⟨x,hx,rfl⟩ := hz
      exact (T i).mem_fatEnclosure D l r (ha i) (hfat i) x (hE i x hx).1 (hE i x hx).2)
    (by intro i; simpa [E',planeCoordinates_image_measure] using hsize i)
    (Q'.indicator (fun _ => (1:ℝ))) (memLp_indicator_const 2 hQ' 1 (Or.inr hQfin')) a havg' t ht
  have hh : ((1/2 : ℝ≥0) : ℝ≥0∞) = (1/2 : ℝ≥0∞) := by norm_num
  simpa only [squareIntegral_indicator Q' hQ', Q', planeCoordinates_image_measure, hh] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeAdmissibility
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Admissibility of the actual thin enclosing rectangle from a slope
popularity witness, with an explicit short horizontal localization. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace LipschitzHilbert

theorem slopeRectangle_popular (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hs : |s| ≤ 1)
    (u : Plane → ℝ) (z : Plane)
    (hz : z ∈ (slopeRectangle c s a b ha hb hba).carrier)
    (hu : |u z-s| ≤ b/(12*a)) :
    z ∈ (slopeRectangle c s a b ha hb hba).popularSet (fun p => slopeDirection (u p)) := by
  let R := slopeRectangle c s a b ha hb hba
  have hl : 0 < R.long := R.short_pos.trans_le R.short_le_long
  have hhalf : R.short/(2*R.long) ≤ (1:ℝ)/2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hl)).mpr
    linarith [R.short_le_long]
  refine ⟨hz,?_⟩
  change Real.cos (R.short/(2*R.long)) ≤ inner ℝ (slopeDirection (u z)) (slopeDirection s)
  exact cos_le_inner_slopeDirection (u z) s _ (hhalf.trans (by linarith [Real.two_le_pi]))
    (hu.trans (slope_rectangle_aperture_ge c s a b ha hb hba hs))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_ClippedEnclosure
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The thin enclosing rectangle for an actual horizontally clipped top
box. The long side is controlled by the testing strip before the published
length restriction is invoked. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace LipschitzHilbert.SlopeBox

theorem mem_thinEnclosure (T : SlopeBox) (D l r : ℝ) (hD : 0 < D)
    (ha : 0 < T.clipLength D l r) (hthin : 2*D*T.width ≤ T.clipLength D l r)
    (z : ℝ × ℝ) (hx : z.1 ∈ Icc l r) (hz : z ∈ T.radialDilation D) :
    planeCoordinates z ∈ (T.thinEnclosure D l r hD ha hthin).carrier := by
  obtain ⟨h1,h2⟩ := T.clipped_coordinates D l r z hx hz
  apply mem_slopeRectangle _ _ _ _ _ _ _ _ h1
  simpa only [show 2*D*T.width/2 = D*T.width by ring] using h2

theorem thinEnclosure_long_le (T : SlopeBox) (D l r : ℝ) (hD : 0 < D)
    (ha : 0 < T.clipLength D l r) (hthin : 2*D*T.width ≤ T.clipLength D l r)
    (hs : |T.slope| ≤ 1) :
    (T.thinEnclosure D l r hD ha hthin).long ≤ 3*(r-l) := by
  exact (slope_rectangle_long_le _ _ _ _ _ _ _ hs).trans
    (mul_le_mul_of_nonneg_left (T.clipLength_le_strip D l r) (by norm_num))

theorem thinEnclosure_volume_le (T : SlopeBox) (D l r : ℝ) (hD : 0 < D)
    (ha : 0 < T.clipLength D l r) (hthin : 2*D*T.width ≤ T.clipLength D l r) :
    volume (T.thinEnclosure D l r hD ha hthin).carrier ≤
      ENNReal.ofReal (8*D^2*T.length*T.width) := by
  apply (volume_slopeRectangle_le _ _ _ _ _ _ _).trans
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_right (T.clipLength_le_dilation D l r)
    (show 0 ≤ 4*D*T.width by have := T.width_pos; positivity)
  nlinarith

theorem clipped_aperture_ge (T : SlopeBox) (D l r : ℝ) (_hD : 0 < D)
    (ha : 0 < T.clipLength D l r) :
    T.width/(12*T.length) ≤ (2*D*T.width)/(12*T.clipLength D l r) := by
  apply (div_le_div_iff₀ (by have := T.length_pos; positivity) (by positivity)).mpr
  have h := mul_le_mul_of_nonneg_left (T.clipLength_le_dilation D l r) T.width_pos.le
  nlinarith

theorem thinEnclosure_admissible (T : SlopeBox) (D l r : ℝ) (hD : 0 < D)
    (ha : 0 < T.clipLength D l r) (hthin : 2*D*T.width ≤ T.clipLength D l r)
    (hs : |T.slope| ≤ 1) (u : Plane → ℝ) (K δ : ℝ≥0) (E : Set (ℝ × ℝ))
    (hE : ∀ z ∈ E, z.1 ∈ Icc l r ∧ z ∈ T.radialDilation D)
    (hclose : ∀ z ∈ E, |u (planeCoordinates z)-T.slope| ≤ T.width/(12*T.length))
    (hlength : 300*(K:ℝ)*(r-l) ≤ 1)
    (harea : (δ:ℝ≥0∞)*ENNReal.ofReal (8*D^2*T.length*T.width) ≤ (volume.prod volume) E) :
    (T.thinEnclosure D l r hD ha hthin).Admissible (fun p => slopeDirection (u p)) K δ := by
  constructor
  · have h := mul_le_mul_of_nonneg_left (T.thinEnclosure_long_le D l r hD ha hthin hs)
      (by positivity : 0 ≤ 100*(K:ℝ))
    nlinarith
  · have hsub : planeCoordinates '' E ⊆
        (T.thinEnclosure D l r hD ha hthin).popularSet (fun p => slopeDirection (u p)) := by
      rintro _ ⟨z,hz,rfl⟩
      apply slopeRectangle_popular _ _ _ _ _ _ _ hs
      · exact T.mem_thinEnclosure D l r hD ha hthin z (hE z hz).1 (hE z hz).2
      · exact (hclose z hz).trans (T.clipped_aperture_ge D l r hD ha)
    calc
      _ ≤ (δ:ℝ≥0∞)*ENNReal.ofReal (8*D^2*T.length*T.width) :=
        mul_le_mul' le_rfl (T.thinEnclosure_volume_le D l r hD ha hthin)
      _ ≤ (volume.prod volume) E := harea
      _ = volume (planeCoordinates '' E) := (planeCoordinates_image_measure E).symm
      _ ≤ _ := measure_mono hsub

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ThinTopTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted tail for actual thin clipped tops, with geometric
admissibility and indicator averages discharged. The remaining data are
exactly the top witnesses, their density and slope agreement, and the
published Lacey--Li estimate. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace LipschitzHilbert

theorem thin_top_weighted_tail (hLL : LaceyLiInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox) (D l r : ℝ)
      (_hD : 0 < D) (_ha : ∀ i, 0 < (T i).clipLength D l r)
      (_hthin : ∀ i, 2*D*(T i).width ≤ (T i).clipLength D l r),
      (∀ i, |(T i).slope| ≤ 1) → ∀ (u : Plane → ℝ) (K δ : ℝ≥0),
      LipschitzWith K u → 0 < δ → δ < 1 →
      300*((2*K:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ (E : ι → Set (ℝ × ℝ)) (w : ι → ℝ≥0∞) (α : ℝ≥0∞),
      (∀ i, MeasurableSet (E i)) → (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation D) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, (δ:ℝ≥0∞)*ENNReal.ofReal (8*D^2*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) →
      (∀ i, α*w i ≤ (volume.prod volume) (E i)) →
      ∀ Q : Set (ℝ × ℝ), MeasurableSet Q → (volume.prod volume) Q ≠ ∞ →
      (∀ z ∈ Q, z.1 ∈ Icc l r) → ∀ a : ι → ℝ,
      (∀ i, 0 ≤ a i) →
      (∀ i, ENNReal.ofReal (a i*(8*D^2*(T i).length*(T i).width)) ≤
        (volume.prod volume) (Q ∩ (T i).radialDilation D)) →
      ∀ t : ℝ≥0, 0 < t →
      (t:ℝ≥0∞)^2*α*(∑ i, if (t:ℝ)<a i then w i else 0) ≤
        (C:ℝ≥0∞)^2/(δ:ℝ≥0∞)*(volume.prod volume) Q := by
  classical
  obtain ⟨C,hC,hbound⟩ := laceyLi_weighted_tail_fintype hLL
  refine ⟨C,hC,?_⟩
  intro ι _ T D l r hD ha hthin hs u K δ hu hδ hδ1 hlength
    E w α hEmeas hdisj hE hclose hpop hsize Q hQ hQfin hstrip a ha0 havg t ht
  let R : ι → Rectangle := fun i => (T i).thinEnclosure D l r hD (ha i) (hthin i)
  let E' : ι → Set Plane := fun i => planeCoordinates '' E i
  let Q' : Set Plane := planeCoordinates '' Q
  have hQ' : MeasurableSet Q' := planeCoordinates.measurableSet_image.mpr hQ
  have hQfin' : volume Q' ≠ ∞ := by simpa [Q', planeCoordinates_image_measure] using hQfin
  have hu' : LipschitzWith (2*K) (fun p => slopeDirection (u p)) :=
    slopeDirection_lipschitz.comp hu
  have hR (i : ι) : (R i).Admissible (fun p => slopeDirection (u p)) (2*K) δ :=
    (T i).thinEnclosure_admissible D l r hD (ha i) (hthin i) (hs i) u (2*K) δ (E i)
      (hE i) (hclose i) hlength (hpop i)
  have hdisj' : Pairwise fun i j => Disjoint (E' i) (E' j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have hxy : x = y := planeCoordinates.injective (hxz.trans hyz.symm)
    subst y
    exact disjoint_left.mp (hdisj hij) hx hy
  have havg' (i : ι) : ENNReal.ofReal (a i) ≤ (R i).average (Q'.indicator (fun _ => (1:ℝ))) := by
    have hinter : ENNReal.ofReal (a i*(8*D^2*(T i).length*(T i).width)) ≤
        volume (planeCoordinates '' (Q ∩ (T i).radialDilation D)) := by
      simpa only [planeCoordinates_image_measure] using havg i
    apply Rectangle.indicator_average_lower (R i) Q'
      (planeCoordinates '' (Q ∩ (T i).radialDilation D)) hQ' _
      (8*D^2*(T i).length*(T i).width) (a i) (by have := (T i).length_pos; have := (T i).width_pos; positivity)
      (ha0 i) ((T i).thinEnclosure_volume_le D l r hD (ha i) (hthin i)) hinter
    rintro z ⟨x,⟨hxQ,hxD⟩,rfl⟩
    exact ⟨mem_image_of_mem _ hxQ,(T i).mem_thinEnclosure D l r hD (ha i) (hthin i) x
      (hstrip x hxQ) hxD⟩
  have h := hbound (fun p => slopeDirection (u p)) (2*K) δ hu'
    (fun p => slopeDirection_norm (u p)) hδ hδ1 ι R hR E' w α
    (fun i => planeCoordinates.measurableSet_image.mpr (hEmeas i)) hdisj'
    (by
      intro i z hz
      obtain ⟨x,hx,rfl⟩ := hz
      exact (T i).mem_thinEnclosure D l r hD (ha i) (hthin i) x (hE i x hx).1 (hE i x hx).2)
    (by intro i; simpa [E',planeCoordinates_image_measure] using hsize i)
    (Q'.indicator (fun _ => (1:ℝ)))
    (memLp_indicator_const 2 hQ' 1 (Or.inr hQfin')) a havg' t ht
  simpa only [squareIntegral_indicator Q' hQ', Q',planeCoordinates_image_measure] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MixedTopTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A mixed family of clipped tops is split by aspect ratio. Both pieces
use the same published Lacey--Li input, and the resulting constant is
uniform in the finite family and dilation. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace LipschitzHilbert

theorem mixed_top_weighted_tail (hLL : LaceyLiInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox)
      (D l r : ℝ), 0 < D → (∀ i, 0 < (T i).clipLength D l r) →
      (∀ i, |(T i).slope| ≤ 1) → ∀ (u : Plane → ℝ) (K δ : ℝ≥0),
      LipschitzWith K u → 0 < δ → δ ≤ 1/2 →
      300*((2*K:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ (E : ι → Set (ℝ × ℝ)) (w : ι → ℝ≥0∞) (α : ℝ≥0∞),
      (∀ i, MeasurableSet (E i)) → (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation D) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, (δ:ℝ≥0∞)*ENNReal.ofReal (8*D^2*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) →
      (∀ i, α*w i ≤ (volume.prod volume) (E i)) →
      ∀ Q : Set (ℝ × ℝ), MeasurableSet Q → (volume.prod volume) Q ≠ ∞ →
      (∀ z ∈ Q, z.1 ∈ Icc l r) → ∀ a : ι → ℝ,
      (∀ i, 0 ≤ a i) →
      (∀ i, ENNReal.ofReal (a i*(8*D^2*(T i).length*(T i).width)) ≤
        (volume.prod volume) (Q ∩ (T i).radialDilation D)) →
      ∀ t : ℝ≥0, 0 < t →
      (t:ℝ≥0∞)^2*α*(∑ i, if (t:ℝ)<a i then w i else 0) ≤
        (C:ℝ≥0∞)^2/(δ:ℝ≥0∞)*(volume.prod volume) Q := by
  classical
  obtain ⟨Ct,hCt,ht⟩ := thin_top_weighted_tail hLL
  obtain ⟨Cf,hCf,hf⟩ := fat_top_weighted_tail hLL
  refine ⟨Ct+Cf, by positivity, ?_⟩
  intro ι _ T D l r hD ha hs u K δ hu hδ hδhalf hlength
    E w α hEmeas hdisj hE hclose hpop hsize Q hQ hQfin hstrip a ha0 havg t hpos
  let p : ι → Prop := fun i => 2*D*(T i).width ≤ (T i).clipLength D l r
  have hthin := ht {i // p i} (fun i => T i) D l r hD (fun i => ha i)
    (fun i => i.property) (fun i => hs i) u K δ hu hδ (hδhalf.trans_lt (by norm_num))
    hlength (fun i => E i) (fun i => w i) α (fun i => hEmeas i)
    (fun i j hij => hdisj (fun heq => hij (Subtype.ext heq)))
    (fun i => hE i) (fun i => hclose i) (fun i => hpop i) (fun i => hsize i)
    Q hQ hQfin hstrip (fun i => a i) (fun i => ha0 i) (fun i => havg i) t hpos
  have hfat := hf {i // ¬p i} (fun i => T i) D l r hD (fun i => ha i)
    (fun i => (lt_of_not_ge i.property).le) (fun i => hs i)
    (fun i => E i) (fun i => w i) α (fun i => hEmeas i)
    (fun i j hij => hdisj (fun heq => hij (Subtype.ext heq)))
    (fun i => hE i) (fun i => hsize i) Q hQ hQfin hstrip
    (fun i => a i) (fun i => ha0 i) (fun i => havg i) t hpos
  have hden : (δ:ℝ≥0∞) ≤ 1/2 := by
    calc
      _ ≤ ((1/2:ℝ≥0):ℝ≥0∞) := ENNReal.coe_le_coe.mpr hδhalf
      _ = _ := by norm_num
  have hfat' : (t:ℝ≥0∞)^2*α*(∑ i : {i // ¬p i}, if (t:ℝ)<a i then w i else 0) ≤
      (Cf:ℝ≥0∞)^2/(δ:ℝ≥0∞)*(volume.prod volume) Q := by
    apply hfat.trans
    gcongr
  have hsplit := Fintype.sum_subtype_add_sum_subtype p
    (fun i => if (t:ℝ)<a i then w i else 0)
  have hsq : (Ct:ℝ≥0∞)^2+(Cf:ℝ≥0∞)^2 ≤ (↑(Ct+Cf):ℝ≥0∞)^2 := by
    exact_mod_cast (show (Ct:ℝ)^2+(Cf:ℝ)^2 ≤ ((Ct+Cf:ℝ≥0):ℝ)^2 by
      push_cast
      nlinarith [mul_nonneg Ct.coe_nonneg Cf.coe_nonneg])
  calc
    _ = (t:ℝ≥0∞)^2*α*(∑ i : {i // p i}, if (t:ℝ)<a i then w i else 0) +
        (t:ℝ≥0∞)^2*α*(∑ i : {i // ¬p i}, if (t:ℝ)<a i then w i else 0) := by
      rw [← mul_add, hsplit]
    _ ≤ (Ct:ℝ≥0∞)^2/(δ:ℝ≥0∞)*(volume.prod volume) Q +
        (Cf:ℝ≥0∞)^2/(δ:ℝ≥0∞)*(volume.prod volume) Q := add_le_add hthin hfat'
    _ = ((Ct:ℝ≥0∞)^2+(Cf:ℝ≥0∞)^2)/(δ:ℝ≥0∞)*(volume.prod volume) Q := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := by gcongr

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopDilationTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaling the mixed rectangle bound by the actual top area gives a
quadratic distribution bound. The density loses exactly two powers of
the dilation radius, which will give a cubic testing cost. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace LipschitzHilbert

theorem top_dilation_square_tail (hLL : LaceyLiInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox)
      (D l r : ℝ), 1 ≤ D → (∀ i, |(T i).slope| ≤ 1) →
      ∀ (u : Plane → ℝ) (K α : ℝ≥0), LipschitzWith K u → 0 < α → α ≤ 1 →
      300*((2*K:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ E : ι → Set (ℝ × ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation D) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal ((α:ℝ)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) →
      ∀ Q : Set (ℝ × ℝ), MeasurableSet Q → (volume.prod volume) Q ≠ ∞ →
      (∀ z ∈ Q, z.1 ∈ Icc l r) → ∀ a : ι → ℝ, (∀ i, 0 ≤ a i) →
      (∀ i, ENNReal.ofReal (a i*(8*D^2*(T i).length*(T i).width)) ≤
        (volume.prod volume) (Q ∩ (T i).radialDilation D)) →
      ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t^2)*(∑ i, if t<a i then
        ENNReal.ofReal ((T i).length*(T i).width) else 0) ≤
      ENNReal.ofReal ((4*(C:ℝ)*D/(α:ℝ))^2 * (volume.prod volume).real Q) := by
  classical
  obtain ⟨C,hC,hbound⟩ := mixed_top_weighted_tail hLL
  refine ⟨C,hC,?_⟩
  intro ι _ T D l r hD hs u K α hu hα hα1 hlength E hEmeas hdisj hE hclose
    hsize Q hQ hQfin hstrip a ha havg t ht
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hαR : (0:ℝ) < α := hα
  let δ : ℝ≥0 := ⟨(α:ℝ)/(8*D^2), by positivity⟩
  have hδ : 0 < δ := by change (0:ℝ) < (α:ℝ)/(8*D^2); positivity
  have hδhalf : δ ≤ 1/2 := by
    change (α:ℝ)/(8*D^2) ≤ ((1/2:ℝ≥0):ℝ)
    norm_num
    apply (div_le_iff₀ (by positivity : 0 < 8*D^2)).mpr
    have hα' : (α:ℝ) ≤ 1 := hα1
    nlinarith [sq_nonneg (D-1)]
  have hED (i : ι) (z : ℝ × ℝ) (hz : z ∈ E i) :
      z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation D :=
    hE i z hz
  have hclip (i : ι) : 0 < (T i).clipLength D l r := by
    apply (T i).clipLength_pos_of_positive_witness D l r (E i) _ (hED i)
    exact lt_of_lt_of_le (by have := (T i).length_pos; have := (T i).width_pos; positivity)
      (hsize i)
  have hpop (i : ι) : (δ:ℝ≥0∞)*ENNReal.ofReal (8*D^2*(T i).length*(T i).width) ≤
      (volume.prod volume) (E i) := by
    rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul δ.coe_nonneg]
    have hid : (δ:ℝ)*(8*D^2*(T i).length*(T i).width) = (α:ℝ)*(T i).length*(T i).width := by
      change ((α:ℝ)/(8*D^2))*(8*D^2*(T i).length*(T i).width) = _
      field_simp
    rw [hid]
    exact hsize i
  let τ : ℝ≥0 := ⟨t, ht.le⟩
  have hm := hbound ι T D l r hDpos hclip hs u K δ hu hδ hδhalf hlength E
    (fun i => ENNReal.ofReal ((T i).length*(T i).width)) α hEmeas hdisj hED hclose
    hpop (by
      intro i
      rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul α.coe_nonneg]
      convert hsize i using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring)
    Q hQ hQfin hstrip a ha havg τ ht
  have hscale : (C:ℝ≥0∞)^2/(δ:ℝ≥0∞)*(volume.prod volume) Q ≤
      (α:ℝ≥0∞)*ENNReal.ofReal ((4*(C:ℝ)*D/(α:ℝ))^2*(volume.prod volume).real Q) := by
    rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_pow C.coe_nonneg,
      ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_div_of_pos (show (0:ℝ)<δ from hδ),
      ← ENNReal.ofReal_toReal hQfin, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul α.coe_nonneg]
    apply ENNReal.ofReal_le_ofReal
    change (C:ℝ)^2/((α:ℝ)/(8*D^2))*(volume.prod volume).real Q ≤ _
    have hid : (C:ℝ)^2/((α:ℝ)/(8*D^2)) = 8*(C:ℝ)^2*D^2/(α:ℝ) := by field_simp
    have hid' : (α:ℝ)*(4*(C:ℝ)*D/(α:ℝ))^2 = 16*(C:ℝ)^2*D^2/(α:ℝ) := by field_simp; ring
    rw [hid, ← mul_assoc, hid']
    gcongr
    norm_num
  apply (ENNReal.mul_le_mul_iff_left (show (α:ℝ≥0∞) ≠ 0 by positivity)
    ENNReal.coe_ne_top).mp
  calc
    _ = (τ:ℝ≥0∞)^2*(α:ℝ≥0∞)*(∑ i, if (τ:ℝ)<a i then
        ENNReal.ofReal ((T i).length*(T i).width) else 0) := by
      have hτ : ENNReal.ofReal t = (τ:ℝ≥0∞) := (ENNReal.coe_nnreal_eq τ).symm
      rw [ENNReal.ofReal_pow ht.le, hτ]
      have hτR : (τ:ℝ) = t := rfl
      rw [hτR]
      ring
    _ ≤ (α:ℝ≥0∞)*ENNReal.ofReal ((4*(C:ℝ)*D/(α:ℝ))^2*(volume.prod volume).real Q) :=
      hm.trans hscale
    _ = _ := mul_comm _ _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_TopDilationPacking
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual intersection averages, weighted by top area, satisfy the cubic
dilation testing estimate. No cardinality factor occurs. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace LipschitzHilbert

theorem top_dilation_packing (hLL : LaceyLiInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox)
      (l r D : ℝ), 1 ≤ D → (∀ i, |(T i).slope| ≤ 1) →
      ∀ (u : Plane → ℝ) (K α : ℝ≥0), LipschitzWith K u → 0 < α → α ≤ 1 →
      300*((2*K:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ E : ι → Set (ℝ × ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation D) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal ((α:ℝ)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) →
      0 < ∑ i, (T i).area →
      ∀ Q : Set (ℝ × ℝ), MeasurableSet Q → (volume.prod volume) Q ≠ ∞ →
      (∀ z ∈ Q, z.1 ∈ Icc l r) →
      (∑ i, (volume.prod volume) (Q ∩ (T i).radialDilation D)) ≤
        ENNReal.ofReal ((C/(α:ℝ))*Real.sqrt (∑ i, (T i).area)*D^3*
          Real.sqrt ((volume.prod volume).real Q)) := by
  classical
  obtain ⟨C,hC,hbound⟩ := top_dilation_square_tail hLL
  refine ⟨64*(C:ℝ), by positivity, ?_⟩
  intro ι _ T l r D hD hs u K α hu hα hα1 hlength E hEmeas hdisj hE hclose hsize
    hS Q hQ hQfin hstrip
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  by_cases hQzero : (volume.prod volume) Q = 0
  · have hi (i : ι) : (volume.prod volume) (Q ∩ (T i).radialDilation D) = 0 :=
      measure_mono_null inter_subset_left hQzero
    simp only [hi, Finset.sum_const_zero]
    exact zero_le
  have hQpos : 0 < (volume.prod volume).real Q := ENNReal.toReal_pos hQzero hQfin
  let B : ℝ := (4*(C:ℝ)*D/(α:ℝ))*Real.sqrt ((volume.prod volume).real Q)
  have hB : 0 < B := by dsimp [B]; exact mul_pos (by positivity) (Real.sqrt_pos.mpr hQpos)
  have hBsq : B^2 = (4*(C:ℝ)*D/(α:ℝ))^2*(volume.prod volume).real Q := by
    dsimp [B]
    rw [mul_pow, Real.sq_sqrt hQpos.le]
  have htail := hbound ι T D l r hD hs u K α hu hα hα1 hlength E hEmeas hdisj hE
    hclose hsize Q hQ hQfin hstrip (fun i => (T i).dilationAverage D Q)
    (fun i => (T i).dilationAverage_nonneg D Q)
    (fun i => ((T i).dilationAverage_normalized D hDpos Q hQfin).le)
  have hlayer := weighted_layer_from_square_tail (fun i => (T i).areaWeight)
    (fun i => (T i).dilationAverage D Q) (fun i => (T i).dilationAverage_nonneg D Q)
    B hB (by simpa using hS) (by
      intro t ht
      simpa only [SlopeBox.ennreal_areaWeight, SlopeBox.area, hBsq] using htail t ht)
  rw [SlopeBox.sum_dilation_intersection_eq T D hDpos Q hQfin]
  calc
    _ ≤ ENNReal.ofReal (8*D^2)*ENNReal.ofReal
        (2*B*Real.sqrt (∑ i, ((T i).areaWeight:ℝ))) := mul_le_mul' le_rfl hlayer
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      simp only [SlopeBox.coe_areaWeight]
      congr 1
      dsimp [B]
      ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PopularTopCount
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth count of popular tops satisfies weak L2 on the
localization strip. The only published input is Lacey--Li; geometric
admissibility, thin/fat splitting, dilation packing, and summation have
all been proved for the actual slope boxes. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace LipschitzHilbert

theorem popular_top_count_weak_two (hLL : LaceyLiInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox)
      (l r R : ℝ), 1 ≤ R → (∀ i, |(T i).slope| ≤ 1) →
      ∀ (u : Plane → ℝ) (K α : ℝ≥0), LipschitzWith K u → 0 < α → α ≤ 1 →
      300*((2*K:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ E : ι → Set (ℝ × ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation R) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal ((α:ℝ)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) →
      ∀ (P d : ℝ), 0 < P → P ≤ R → 4 ≤ d →
      ∀ t : ℝ, 0 < t →
      (volume.prod volume) ({z | z.1 ∈ Icc l r} ∩ {z | t < ∑ i, (T i).weight P d z}) ≤
        ENNReal.ofReal ((2*4^d*(C/(α:ℝ))*Real.sqrt (∑ i, (T i).area)*R^3)^2/t^2) := by
  classical
  obtain ⟨C,hC,hpack⟩ := top_dilation_packing hLL
  refine ⟨C,hC,?_⟩
  intro ι _ T l r R hR hs u K α hu hα hα1 hlength E hEmeas hdisj hE hclose hsize
    P d hP hPR hd t ht
  by_cases hne : Nonempty ι
  · let := hne
    have hS : 0 < ∑ i, (T i).area :=
      Finset.sum_pos (fun i _ => (T i).area_pos) Finset.univ_nonempty
    have hb := top_count_weak_two_on_set T {z | z.1 ∈ Icc l r}
      (measurableSet_Icc.preimage measurable_fst) P R d
      ((C/(α:ℝ))*Real.sqrt (∑ i, (T i).area)) hP hPR hd (by positivity) (by
        intro Q hQ hQfin hQsub n
        have hRn : 1 ≤ R*2^n := one_le_mul_of_one_le_of_one_le hR
          (one_le_pow₀ (by norm_num))
        have hED (i : ι) (z : ℝ × ℝ) (hz : z ∈ E i) :
            z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation (R*2^n) := by
          refine ⟨(hE i z hz).1, ?_⟩
          change (T i).radius z ≤ R*2^n
          exact ((hE i z hz).2 : (T i).radius z ≤ R).trans
            (le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num)))
        have hp := hpack ι T l r (R*2^n) hRn hs u K α hu hα hα1 hlength E hEmeas hdisj hED hclose
          hsize hS Q hQ hQfin (fun z hz => hQsub hz)
        convert hp using 1) t ht
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  · let : IsEmpty ι := not_nonempty_iff.mp hne
    have he : {z : ℝ × ℝ | t < ∑ i, (T i).weight P d z} = ∅ := by
      ext z
      simp only [Finset.univ_eq_empty, Finset.sum_empty, mem_ofPred_eq, mem_empty_iff_false,
        iff_false]
      exact not_lt_of_ge ht.le
    rw [he, inter_empty, measure_empty]
    exact zero_le

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PopularTopCountPowers
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The count exponent C_as + 3 max(k,C_as) in the manuscript follows
from the actual witness density and a common polynomial base dilation. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace LipschitzHilbert

theorem popular_top_count_powers (hLL : LaceyLiInput) (a k d : ℝ)
    (ha : 0 ≤ a) (hd : 4 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox) (l r : ℝ),
      (∀ i, |(T i).slope| ≤ 1) → ∀ (u : Plane → ℝ) (K : ℝ≥0),
      LipschitzWith K u → 300*((2*K:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ E : ι → Set (ℝ × ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ (T i).radius z ≤ L^a) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal (L^(-a)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) → ∀ t : ℝ, 0 < t →
      (volume.prod volume) ({z | z.1 ∈ Icc l r} ∩ {z | t < ∑ i, (T i).weight (L^k) d z}) ≤
        ENNReal.ofReal ((C*L^(a+3*max k a)*Real.sqrt (∑ i, (T i).area))^2/t^2) := by
  classical
  obtain ⟨C,hC,hcount⟩ := popular_top_count_weak_two hLL
  refine ⟨16*4^d*C, by positivity, ?_⟩
  intro L hL ι _ T l r hs u K hu hlength E hEmeas hdisj hE hclose hsize t ht
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  let α : ℝ≥0 := ⟨L^(-a), by positivity⟩
  have hα : 0 < α := by change (0:ℝ)<L^(-a); positivity
  have hα1 : α ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hpka : L^k ≤ L^(max k a) := Real.rpow_le_rpow_of_exponent_le hL (le_max_left _ _)
  have hpaa : L^a ≤ L^(max k a) := Real.rpow_le_rpow_of_exponent_le hL (le_max_right _ _)
  have hR : 1 ≤ 2*L^(max k a) := by
    have hp : 1 ≤ L^(max k a) := Real.one_le_rpow hL (ha.trans (le_max_right _ _))
    linarith
  have hPR : L^k ≤ 2*L^(max k a) := hpka.trans (by nlinarith [Real.rpow_nonneg hLpos.le (max k a)])
  have hER (i : ι) (z : ℝ × ℝ) (hz : z ∈ E i) :
      z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation (2*L^(max k a)) := by
    refine ⟨(hE i z hz).1, ?_⟩
    change (T i).radius z ≤ 2*L^(max k a)
    exact (hE i z hz).2.trans (hpaa.trans (by nlinarith [Real.rpow_nonneg hLpos.le (max k a)]))
  have h := hcount ι T l r (2*L^(max k a)) hR hs u K α hu hα hα1 hlength E
    hEmeas hdisj hER hclose hsize (L^k) d (by positivity) hPR hd t ht
  have hp : L^a*(L^(max k a))^3 = L^(a+3*max k a) := by
    rw [← Real.rpow_mul_natCast hLpos.le]
    rw [← Real.rpow_add hLpos]
    congr 1
    norm_num [mul_comm]
  have heq : 2*4^d*(C/(α:ℝ))*Real.sqrt (∑ i, (T i).area)*(2*L^(max k a))^3 =
      (16*4^d*C)*L^(a+3*max k a)*Real.sqrt (∑ i, (T i).area) := by
    change 2*4^d*(C/L^(-a))*Real.sqrt (∑ i, (T i).area)*(2*L^(max k a))^3 = _
    rw [Real.rpow_neg hLpos.le, div_inv_eq_mul, ← hp]
    ring
  simpa only [heq] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CountThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the proved weak square tail and total-area budget into the
manuscript's polynomial count cutoff, with no top-cardinality loss. -/

noncomputable section
namespace LipschitzHilbert

theorem weak_two_polynomial_threshold (C L a s H N F S : ℝ)
    (hC : 0 ≤ C) (hL : 1 ≤ L) (hCL : C ≤ L) (hN : 0 < N)
    (hF : 0 ≤ F) (hS : 0 ≤ S) (harea : S ≤ L^s*N^2*F) :
    (C*L^a*Real.sqrt S)^2/(N*L^(a+(s+H)/2+1))^2 ≤ L^(-H)*F := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let b := a+(s+H)/2+1
  have hden : 0 < (N*L^b)^2 := by positivity
  change (C*L^a*Real.sqrt S)^2/(N*L^b)^2 ≤ _
  apply (div_le_iff₀ hden).mpr
  have hCa : C^2 ≤ L^2 := pow_le_pow_left₀ hC hCL 2
  have ha2 : (L^a)^2 = L^(2*a) := by
    rw [← Real.rpow_mul_natCast hL0.le]
    congr 1
    ring
  have hb2 : (L^b)^2 = L^(2*b) := by
    rw [← Real.rpow_mul_natCast hL0.le]
    congr 1
    ring
  have hpower : L^2*L^(2*a)*L^s = L^(-H)*L^(2*b) := by
    rw [← Real.rpow_two L, ← Real.rpow_add hL0, ← Real.rpow_add hL0,
      ← Real.rpow_add hL0]
    congr 1
    dsimp [b]
    ring
  rw [mul_pow, mul_pow, Real.sq_sqrt hS, ha2, mul_pow, hb2]
  calc
    C^2*L^(2*a)*S ≤ C^2*L^(2*a)*(L^s*N^2*F) :=
      mul_le_mul_of_nonneg_left harea (by positivity)
    _ ≤ L^2*L^(2*a)*(L^s*N^2*F) := by gcongr
    _ = (L^(-H)*F)*(N^2*L^(2*b)) := by
      calc
        _ = (L^2*L^(2*a)*L^s)*(N^2*F) := by ring
        _ = _ := by rw [hpower]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MaskIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrate the actual finite mask error using the weak L2 top count.
Integrability is proved from the distribution bound. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem mask_error_integral {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : μ univ ≠ 0)
    (F : ι → Ω → EuclideanSpace ℂ κ) (mask weight : ι → Ω → ℝ)
    (hFmeas : ∀ i, Measurable (F i)) (hmmeas : ∀ i, Measurable (mask i))
    (hwmeas : ∀ i, Measurable (weight i)) (T ε K : ℝ)
    (hT : 0 ≤ T) (hε : 0 ≤ ε) (hK : 0 < K)
    (hw : ∀ i x, 0 ≤ weight i x)
    (hF : ∀ᵐ x ∂μ, ∀ i, ‖F i x‖ ≤ T*(weight i x)^8)
    (hmask : ∀ i x, |1-mask i x| * T*(weight i x)^7 ≤ ε)
    (hweak : ∀ s : ℝ, 0 < s →
      μ {x | s < ∑ i, weight i x} ≤ ENNReal.ofReal (K^2/s^2)) :
    Integrable (fun x => ‖(∑ i, F i x)-(∑ i, mask i x • F i x)‖) μ ∧
      (∫ x, ‖(∑ i, F i x)-(∑ i, mask i x • F i x)‖ ∂μ) ≤
        2*ε*K*Real.sqrt ((μ univ).toReal) := by
  let error : Ω → EuclideanSpace ℂ κ := fun x => (∑ i, F i x)-(∑ i, mask i x • F i x)
  let count : Ω → ℝ := fun x => ∑ i, weight i x
  have he : Measurable error := by
    apply Measurable.sub
    · exact Finset.measurable_sum _ (fun i _ => hFmeas i)
    · exact Finset.measurable_sum _ (fun i _ => (hmmeas i).smul (hFmeas i))
  have hc : Measurable count := Finset.measurable_sum _ (fun i _ => hwmeas i)
  have hc0 (x : Ω) : 0 ≤ count x := Finset.sum_nonneg (fun i _ => hw i x)
  have hp : ∀ᵐ x ∂μ, ‖error x‖ ≤ ε*count x := hF.mono fun x hx =>
    norm_sum_sub_mask_le (fun i => F i x) (fun i => mask i x) (fun i => weight i x)
      T ε hT hε (fun i => hw i x) hx (fun i => hmask i x)
  have hcount := weak_two_lintegral μ hμ count hc.aemeasurable
    (Filter.Eventually.of_forall hc0) K hK hweak
  have hb : (∫⁻ x, ENNReal.ofReal ‖error x‖ ∂μ) ≤
      ENNReal.ofReal (2*ε*K*Real.sqrt ((μ univ).toReal)) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (ε*count x) ∂μ :=
        lintegral_mono_ae (hp.mono fun _ h => ENNReal.ofReal_le_ofReal h)
      _ = ENNReal.ofReal ε*(∫⁻ x, ENNReal.ofReal (count x) ∂μ) := by
        simp_rw [ENNReal.ofReal_mul hε]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ε*ENNReal.ofReal (2*K*Real.sqrt ((μ univ).toReal)) :=
        mul_le_mul' le_rfl hcount
      _ = _ := by rw [← ENNReal.ofReal_mul hε]; congr 1; ring
  have hint : Integrable (fun x => ‖error x‖) μ :=
    ⟨he.norm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun x => norm_nonneg (error x)))).mpr
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩
  refine ⟨hint,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun x => norm_nonneg (error x)))] at hb
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun x => norm_nonneg (error x))),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*ε*K*Real.sqrt ((μ univ).toReal))] using hreal

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeMaskIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sinc-masked slope-box synthesis on a finite testing
measure. The amplitude bound is required only almost everywhere on that
measure, allowing restriction to the good testing set. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem exists_slope_mask_integral_above (C H A1 D M : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H) (hD : 0 < D) :
    ∃ A L0 : ℝ, M < A ∧ 2 < A ∧ 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
        (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ], μ univ ≠ 0 →
      ∀ (T : ι → SlopeBox) (F : ι → ℝ × ℝ → EuclideanSpace ℂ κ),
      (∀ i, Measurable (F i)) →
      (∀ᵐ z ∂μ, ∀ i, ‖F i z‖ ≤ L^C*((T i).weight (L^A1) D z)^8) →
      ∀ K : ℝ, 0 < K →
      (∀ s : ℝ, 0 < s → μ {z | s < ∑ i, (T i).weight (L^A1) D z} ≤
        ENNReal.ofReal (K^2/s^2)) →
      Integrable (fun z => ‖(∑ i, F i z)-(∑ i, (T i).mask L A z • F i z)‖) μ ∧
        (∫ z, ‖(∑ i, F i z)-(∑ i, (T i).mask L A z • F i z)‖ ∂μ) ≤
          2*L^(-H)*K*Real.sqrt ((μ univ).toReal) := by
  obtain ⟨A,L0,hM,hA,hL0,hmask⟩ := exists_mask_parameters_above C H A1 D M hC hH hD
  refine ⟨A,L0,hM,hA,hL0,?_⟩
  intro L hL ι κ _ _ μ _ hμ T F hFmeas hF K hK hweak
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < L0) hL
  apply mask_error_integral μ hμ F (fun i => (T i).mask L A)
    (fun i => (T i).weight (L^A1) D) hFmeas
    (fun i => ((T i).mask_continuous L A).measurable)
    (fun i => ((T i).weight_continuous _ D (Real.rpow_pos_of_pos hLpos _)).measurable)
    (L^C) (L^(-H)) K (by positivity) (by positivity) hK
    (fun i z => ((T i).weight_pos (Real.rpow_pos_of_pos hLpos _) D z).le) hF
  · intro i z
    exact hmask L hL ((T i).horizontal z) ((T i).transverse z)
  · exact hweak

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MaskNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the weak-L2 mask error by the source relation between
total top area and the two testing measures. -/

noncomputable section
namespace LipschitzHilbert

theorem sqrt_area_product (L s N F G S : ℝ) (hL : 0 < L) (hN : 0 ≤ N)
    (hF : 0 ≤ F) (hGle : G ≤ F) (hS : S ≤ L^s*N^2*F) :
    Real.sqrt S*Real.sqrt G ≤ L^(s/2)*N*F := by
  have hroot : Real.sqrt (L^s) = L^(s/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL.le]
    congr 1
    ring
  calc
    _ ≤ Real.sqrt (L^s*N^2*F)*Real.sqrt F :=
      mul_le_mul (Real.sqrt_le_sqrt hS) (Real.sqrt_le_sqrt hGle)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = L^(s/2)*N*F := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ L^s*N^2),
        Real.sqrt_mul (Real.rpow_nonneg hL.le _), Real.sqrt_sq hN, hroot]
      calc
        _ = L^(s/2)*N*(Real.sqrt F*Real.sqrt F) := by ring
        _ = _ := by rw [Real.mul_self_sqrt hF]

theorem mask_error_normalization (L C e s H N F G S : ℝ)
    (hL : 0 < L) (hC : 0 ≤ C) (hCL : 2*C ≤ L^2) (hN : 0 ≤ N)
    (hF : 0 ≤ F) (hGle : G ≤ F) (hS : S ≤ L^s*N^2*F) :
    2*L^(-(H+e+s/2+2))*(C*L^e*Real.sqrt S)*Real.sqrt G ≤ L^(-H)*N*F := by
  have harea := sqrt_area_product L s N F G S hL hN hF hGle hS
  have hpower : L^(-(H+e+s/2+2))*L^e*L^(s/2) = L^(-H-2) := by
    rw [← Real.rpow_add hL, ← Real.rpow_add hL]
    congr 1
    ring
  have hpower2 : L^2*L^(-H-2) = L^(-H) := by
    rw [← Real.rpow_two L, ← Real.rpow_add hL]
    congr 1
    ring
  calc
    _ = (2*C*L^(-(H+e+s/2+2))*L^e)*(Real.sqrt S*Real.sqrt G) := by ring
    _ ≤ (2*C*L^(-(H+e+s/2+2))*L^e)*(L^(s/2)*N*F) :=
      mul_le_mul_of_nonneg_left harea (by positivity)
    _ = (2*C*L^(-H-2))*(N*F) := by
      rw [show (2*C*L^(-(H+e+s/2+2))*L^e)*(L^(s/2)*N*F) =
        (2*C)*(L^(-(H+e+s/2+2))*L^e*L^(s/2))*(N*F) by ring, hpower]
    _ ≤ (L^2*L^(-H-2))*(N*F) := by gcongr
    _ = L^(-H)*N*F := by rw [hpower2]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PopularCountDiscard
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The count cutoff used in concentration has the requested relative
area cost, from the actual popular witnesses and Lacey--Li input. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert

theorem popular_top_count_discard (hLL : LaceyLiInput) (a k d s H : ℝ)
    (ha : 0 ≤ a) (hd : 4 ≤ d) (hs : 0 ≤ s) (hH : 0 ≤ H) :
    ∃ Cn L0 : ℝ, 0 < Cn ∧ 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox) (l r : ℝ),
      (∀ i, |(T i).slope| ≤ 1) → ∀ (u : Plane → ℝ) (K : ℝ≥0),
      LipschitzWith K u → 300*((2*K:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ E : ι → Set (ℝ × ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ (T i).radius z ≤ L^a) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal (L^(-a)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) →
      ∀ (N : ℝ) (F : Set (ℝ × ℝ)), 0 < N →
      (∀ z ∈ F, z.1 ∈ Icc l r) →
      (∑ i, (T i).area) ≤ L^s*N^2*(volume.prod volume).real F →
      (volume.prod volume) (F ∩ {z | N*L^Cn < ∑ i, (T i).weight (L^k) d z}) ≤
        ENNReal.ofReal (L^(-H)*(volume.prod volume).real F) := by
  obtain ⟨C,hC,hcount⟩ := popular_top_count_powers hLL a k d ha hd
  let A := a+3*max k a
  let Cn := A+(s+H)/2+1
  have hA : 0 ≤ A := by dsimp [A]; nlinarith [le_max_right k a]
  have hCn : 0 < Cn := by dsimp [Cn]; positivity
  refine ⟨Cn,max 1 C,hCn,le_max_left _ _,?_⟩
  intro L hL ι _ T l r hslopes u K hu hlength E hE hdisj hinside hclose hsize N F hN hFstrip hS
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hCL : C ≤ L := (le_max_right _ _).trans hL
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have htail := hcount L hL1 ι T l r hslopes u K hu hlength E hE hdisj hinside hclose hsize
    (N*L^Cn) (mul_pos hN (Real.rpow_pos_of_pos hLpos _))
  apply (measure_mono (show F ∩ {z | N*L^Cn < ∑ i, (T i).weight (L^k) d z} ⊆
      {z | z.1 ∈ Icc l r} ∩ {z | N*L^Cn < ∑ i, (T i).weight (L^k) d z} from
    fun z hz => ⟨hFstrip z hz.1,hz.2⟩)).trans
  apply htail.trans
  exact ENNReal.ofReal_le_ofReal (weak_two_polynomial_threshold C L A s H N
    ((volume.prod volume).real F) (∑ i, (T i).area) hC.le hL1 hCL hN measureReal_nonneg
      (Finset.sum_nonneg fun i _ => (T i).area_pos.le) hS)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopAreaDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the exponential total-top-area exception to a small fraction
of the testing set, using only the manuscript's area and disparity bounds. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_top_area_factor (b H : ℝ) :
    ∀ᶠ L : ℝ in atTop, L^b*Real.exp (-6*L) ≤ (1/2)*L^(-H) := by
  have hsmall := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b+H) 6 (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    hsmall.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with L hL hsmall
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have h := mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_nonneg hL0.le (-H))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [mul_right_comm, ← Real.rpow_add hL0]
  congr 2
  ring

theorem top_area_discard_numeric (L b H N F S : ℝ)
    (hL : 0 < L) (hN : 0 ≤ N) (hF : 0 ≤ F)
    (hNupper : N ≤ Real.exp (2*L)) (harea : S ≤ L^b*N^2*F)
    (hsmall : L^b*Real.exp (-6*L) ≤ (1/2)*L^(-H)) :
    Real.exp (-10*L)*S ≤ (1/2)*L^(-H)*F := by
  have hNsq := pow_le_pow_left₀ hN hNupper 2
  have hExp : (Real.exp (2*L))^2 = Real.exp (4*L) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hExp] at hNsq
  calc
    _ ≤ Real.exp (-10*L)*(L^b*N^2*F) :=
      mul_le_mul_of_nonneg_left harea (Real.exp_pos _).le
    _ ≤ Real.exp (-10*L)*(L^b*Real.exp (4*L)*F) := by gcongr
    _ = (L^b*Real.exp (-6*L))*F := by
      rw [show Real.exp (-10*L)*(L^b*Real.exp (4*L)*F) =
        L^b*(Real.exp (-10*L)*Real.exp (4*L))*F by ring, ← Real.exp_add]
      rw [show -10*L+4*L = -6*L by ring]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hF

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineWeightAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested line averaging against the manuscript's actual top weight. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem continuous_weight (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) :
    Continuous (T.weight K D) := by
  have hr : Continuous (fun z => 1 + T.radius z / K) := by
    unfold radius horizontal transverse
    fun_prop
  unfold weight
  apply continuous_const.mul
  exact hr.rpow_const fun z => Or.inl (ne_of_gt (by
    have h := T.radius_nonnegative z
    positivity))

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketLatticeData
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite packet family before choosing a reference direction.
There is no small-shear condition on its slopes. That condition is proved
only for the labels retained in a short reference cone. -/
noncomputable section
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone * w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F / w)

local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceFamily_actualZ (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).actualZ j l u = P.actualZ j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u +
      (oldSlope - newSlope) * P.actualX j
        (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  dsimp [SourceLabeledLattice.actualZ, actualZ, actualX, referenceFamily,
    SourceLabeledLattice.length, length]
  ring

theorem referenceFamily_physicalPacket (j : Fin N) (l : (Q).labels j)
    (u : Item j l) (k : κ) :
    (Q).physicalPacket newSlope j l u k = P.physicalPacket oldSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k := by
  let l₀ := P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l
  have hx := P.referenceFamily_actualX oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  have hz := P.referenceFamily_actualZ oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  unfold SourceLabeledLattice.physicalPacket physicalPacket
  rw [hx, hz]
  have hc : P.actualZ j l₀ u + (oldSlope - newSlope) * P.actualX j l₀ u +
      newSlope * P.actualX j l₀ u = P.actualZ j l₀ u + oldSlope * P.actualX j l₀ u := by ring
  have hs : newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope)) =
      oldSlope + P.rowSlope j l₀ := by ring
  change physicalPlanarPacket (P.profile j l₀ u k) _ _ (P.length j) P.width
    (newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope))) (P.frequency k) _ _ = _
  rw [hc, hs]

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledRawEnvelope
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carrier-free raw bounds for the original labeled lattices, before
any bound on the total number of labels is imposed. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem raw_eq_physical_slice (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (y t : ℝ) :
    P.raw i j l u k y = planarSchwartzSlice
      (planarCovariantJet (P.physicalPacket t j l u k) (P.frequency k) P.scale i) y t := by
  have h := physicalPlanarPacket_jet_slice (P.profile j l u k) (P.actualX j l u)
    (P.actualZ j l u+t*P.actualX j l u) (P.length j) P.width
    (t+P.rowSlope j l) (P.frequency k) P.scale y t (P.length_pos j).ne' P.width_pos.ne' i
  have hc : P.actualZ j l u+t*P.actualX j l u-t*P.actualX j l u = P.actualZ j l u := by ring
  have hd : t-(t+P.rowSlope j l) = -P.rowSlope j l := by ring
  simpa only [hc,hd,raw,physicalPacket] using h.symm

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analyzing coefficients for unrestricted packet lattices and their
exact transport to the local reference lattice. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F) (hwide : cone*w≤P.width)
  (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceFamily_multiplier_coefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope
      (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
      v g j l u =
    P.physicalMultiplierCoefficient oldSlope b v g j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  ext k
  simp only [SourceLabeledLattice.physicalMultiplierCoefficient,physicalMultiplierCoefficient,
    analyzingCoefficient,WithLp.ofLp_toLp]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  have hp := congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => f z)
    (P.referenceFamily_physicalPacket oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency j l u k)
  dsimp only [referenceSelector]
  rw [hp]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceConditions
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen main coefficients vanish outside the fixed selector cone.
Restricting the main reference family to that cone is an exact identity;
its carrier bound therefore does not inherit the wide error cone. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

/-- A finite source sum supported on the reference labels equals the
sum in the literal restricted family. -/
theorem sum_referenceLabels_of_zero {E : Type*} [AddCommMonoid E]
    (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E)
    (hzero : ∀ l, ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l →
      ∀ u, f l u = 0) :
    (∑ l : P.referenceLabels oldSlope newSlope referenceLength cone w j,
      ∑ u : Item j l, f (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have hrestrict := Equiv.sum_comp (P.referenceLabelsEquiv oldSlope newSlope referenceLength cone w j)
    (fun l => ∑ u : Item j l.val, f l.val u)
  have hz : (∑ l : {l : P.labels j //
      ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l},
      ∑ u : Item j l.val, f l.val u) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    exact Finset.sum_eq_zero (fun u _ => hzero l.val l.property u)
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (P.referenceCondition oldSlope newSlope referenceLength cone w j)
    (fun l : P.labels j => ∑ u : Item j l, f l u)
  rw [hz,add_zero] at hsum
  exact hrestrict.trans hsum

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned top restrictions with common label and item types. The top
is part of the label, so each top family contains exactly its own packets
and the family-valued concentration and path estimates apply literally. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem sum_assignedTopPackets {E : Type*} [AddCommMonoid E]
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
    (f : P.PacketIndex → E) :
    (∑ q : (P.assignedTopFamily packets assigned top).PacketIndex,
      f ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩) =
      ∑ q ∈ packets.filter (fun q => assigned q = top), f q := by
  have h := Equiv.sum_comp (P.assignedTopPacketEquiv packets assigned top)
    (fun q => f q.val)
  exact h.trans (Finset.sum_subtype _ (p := fun q =>
    q ∈ packets.filter (fun q => assigned q = top)) (by simp) f).symm

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceProperties
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical selector centers are invariant under recentering.
Restricting to the reference cone can only decrease their local count. -/

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w

theorem referenceFamily_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l)) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u :=
  P.referenceFamily_multiplier_coefficient oldSlope newSlope R cone w F hw hcone hF hwide hfrequency b v f j l u

/-- A selected set supported in the reference cone has the identical
sum after the literal label restriction, including empty item fibers. -/
theorem sum_referenceFamily_selected {E : Type*} [AddCommMonoid E]
    (S : Finset P.PacketIndex) (f : P.PacketIndex → E)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1) :
    (∑ u ∈ (Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S),
      f ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩) = ∑ u ∈ S, f u := by
  have hs : (Finset.univ.filter fun u : P.PacketIndex => u ∈ S) = S := by
    ext u
    simp
  conv_rhs => rw [← hs,Finset.sum_filter]
  simp only [Finset.sum_filter,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  exact P.sum_referenceLabels_of_zero oldSlope newSlope R cone w j
    (fun l u => if (⟨j,⟨l,u⟩⟩ : P.PacketIndex) ∈ S then f ⟨j,⟨l,u⟩⟩ else 0)
    (by
      intro l hl u
      rw [ite_eq_right]
      exact fun hu => hl (hS ⟨j,⟨l,u⟩⟩ hu))

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopSelector
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The assigned-top constructor preserves the original selectors,
packet spectra, and local label count. Its geometry is supplied by the
actual selected packets; the global longest-scale bound remains explicit. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)

theorem assignedTopLabel_first (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j) : l.val.1 = top :=
  Finset.mem_singleton.mp (Finset.mem_product.mp l.property).1

theorem assignedTopItem_mem (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    (⟨j,⟨l.val.2,u.val⟩⟩ : P.PacketIndex) ∈ packets := u.property.1

theorem assignedTopItem_assignment (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    assigned ⟨j,⟨l.val.2,u.val⟩⟩ = top :=
  u.property.2.trans (P.assignedTopLabel_first packets assigned top j l)


section Reference
variable (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
  (hF : 0 ≤ F) (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => referenceFamily (P.assignedTopFamily packets assigned top) oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => referenceOriginalLabel (P.assignedTopFamily packets assigned top) oldSlope newSlope R cone w

theorem assignedTopReference_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (l : (Q).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l).val.2) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l).val.2 u.val :=
  (P.assignedTopFamily packets assigned top).referenceFamily_physicalMultiplierCoefficient oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency (P.assignedTopSelector packets assigned top b) v f j l u

end Reference

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledCrossIdentity
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual-square and unary-variation estimates use exactly the
same original analyzing coefficients and alternate physical synthesis.
The mask is applied to the synthesized vector, with no coefficient change. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)

theorem physicalCrossPacketValue_zero (y x : ℝ) (q : P.PacketIndex) :
    P.physicalCrossPacketValue alt hAlt t b v g 0 (x,y+t*x) q =
      WithLp.toLp 2 (fun k => P.physicalMultiplierCoefficient t b v g q.1 q.2.1 q.2.2 k*
        (P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k (x,y+t*x)) := by
  ext k
  have hw := congrArg (fun f : SchwartzMap ℝ ℂ => f x)
    ((P.withProfile alt hAlt).raw_eq_physical_slice 0 q.1 q.2.1 q.2.2 k y t)
  change (P.withProfile alt hAlt).raw 0 q.1 q.2.1 q.2.2 k y x =
    (P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k (x,y+t*x) at hw
  have hy : (y+t*x)-t*x = y := by ring
  simp only [physicalCrossPacketValue,rawPacketValue,WithLp.ofLp_toLp,hy,hw]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceCross
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local reference restriction preserves the actual two-profile packet
operator, including its masked analyzing coefficient. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F) (hwide : cone*w≤P.width)
  (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceAlt_physicalPacket
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (j : Fin N) (l : (Q).labels j) (a : Item j l) (k : κ) :
    ((Q).withProfile
      (P.referenceAlt oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt)
      (P.referenceAlt_bound oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt hAlt)).physicalPacket
        newSlope j l a k =
    (P.withProfile alt hAlt).physicalPacket oldSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) a k := by
  exact (P.withProfile alt hAlt).referenceFamily_physicalPacket
    oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency j l a k

theorem referenceFamily_crossPacketValue
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (a : Item j l) (z : ℝ×ℝ) :
    (Q).physicalCrossPacketValue
      (P.referenceAlt oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt)
      (P.referenceAlt_bound oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt hAlt)
      newSlope
      (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
      v g 0 z ⟨j,l,a⟩ =
    P.crossPacketValue alt hAlt oldSlope b v g z
      ⟨j,P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l,a⟩ := by
  have he := (Q).physicalCrossPacketValue_zero
    (P.referenceAlt oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt)
    (P.referenceAlt_bound oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt hAlt)
    newSlope
    (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
    v g (z.2-newSlope*z.1) z.1 ⟨j,l,a⟩
  have hz : (z.1,z.2-newSlope*z.1+newSlope*z.1)=z := by
    ext
    · rfl
    · dsimp only
      ring
  rw [hz] at he
  rw [he]
  apply WithLp.ofLp_injective
  funext k
  change (Q).physicalMultiplierCoefficient newSlope
    (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
      v g j l a k *
    ((Q).withProfile
      (P.referenceAlt oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt)
      (P.referenceAlt_bound oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt hAlt)).physicalPacket
        newSlope j l a k z = _
  rw [P.referenceFamily_multiplier_coefficient oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency b v g j l a,
    P.referenceAlt_physicalPacket oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency alt hAlt j l a k]
  rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAssignedStoppedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supported assigned-top estimates apply to the original individual
physical packets. These identities retain their analyzing coefficients,
alternate profiles, stopping levels, masks and source transitions. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => assignedReferenceFamily P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

local notation "orig" => assignedReferenceOriginalLabel P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

local notation "alts" => assignedReferenceAlternate P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt

include hAlt in
theorem assignedReferenceAlternate_bound (top : τ) (j : Fin N) (l : (Q top).labels j)
    (u : P.AssignedTopItem packets assigned j l) (k : κ) :
    planarProfileConstant (alts top j l u k) (2*(Q top).order) ≤ (Q top).profileBound :=
  hAlt j (orig top j l) u.val k

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataMaskedValue
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal physical top masks for unrestricted packets. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
variable (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

theorem physicalMaskedValue_eq_cross_at (z : ℝ×ℝ) (q : P.PacketIndex) :
    P.physicalMaskedValue alt hAlt t b v g T L A z q =
      (T q.1 q.2.1 q.2.2).mask L A z • P.crossPacketValue alt hAlt t b v g z q := by
  ext k
  simp only [physicalMaskedValue,crossPacketValue,WithLp.ofLp_toLp,PiLp.smul_apply,
    Complex.real_smul]
  ring

omit T L A in
 theorem crossPacketValue_continuous (q : P.PacketIndex) :
    Continuous (fun z => P.crossPacketValue alt hAlt t b v g z q) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  exact continuous_const.mul
    ((P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k).continuous

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedMaskSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact regrouping of unrestricted physical packets in their assigned
reference families. The analyzing integrals and top masks are unchanged. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem crossSum_eq_rawInterval (P : SourceLabeledLattice N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    (∑ q : P.PacketIndex, P.physicalCrossPacketValue alt hAlt t b v f 0 z q) =
      (P.withProfile alt hAlt).rawInterval (P.physicalMultiplierCoefficient t b v f)
        0 0 N z.1 (z.2-t*z.1) := by
  ext k
  simp only [physicalCrossPacketValue,rawPacketValue,rawInterval,planarPacketInterval,
    bandIntervalSignal,scalarBandPartial,planarPacketBand,WithLp.ofLp_sum,
    WithLp.ofLp_toLp,Finset.sum_apply,Fintype.sum_sigma,Fin.is_lt,ite_true, if_true,
    Nat.not_lt_zero,ite_false, if_false,Finset.sum_const_zero,sub_zero]

end SourceLabeledLattice
namespace PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F) (hwide : cone*w≤P.width)
  (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.assignedReferenceFamily packets assigned T t R cone w F
  hw hcone hF hwide hfrequency
local notation "orig" => P.assignedReferenceOriginalLabel packets assigned T t R cone w F
  hw hcone hF hwide hfrequency
local notation "alts" => P.assignedReferenceAlternate packets assigned T t R cone w F
  hw hcone hF hwide hfrequency alt
local notation "halt" => P.assignedReferenceAlternate_bound packets assigned T t R cone w F
  hw hcone hF hwide hfrequency alt hAlt

theorem assignedCrossSum_eq_rawInterval (z : ℝ×ℝ) (top : τ)
    (hcondition : ∀ q ∈ packets, assigned q=top →
      P.referenceCondition t (T top).slope (R top) cone w q.1 q.2.1) :
    (∑ q ∈ packets.filter (fun q => assigned q=top), P.crossPacketValue alt hAlt t b v f z q) =
      ((Q top).withProfile (alts top) (halt top)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient t b v f j (orig top j l) u.val)
        0 0 N z.1 (z.2-(T top).slope*z.1) := by
  let A := P.assignedTopFamily packets assigned top
  let a := P.assignedTopAlternate packets assigned alt top
  let ha := P.assignedTopAlternate_bound packets assigned alt hAlt top
  have hcond : ∀ q ∈ (Finset.univ : Finset A.PacketIndex),
      A.referenceCondition t (T top).slope (R top) cone w q.1 q.2.1 := by
    intro q _
    exact hcondition ⟨q.1,q.2.1.val.2,q.2.2.val⟩
      (P.assignedTopItem_mem packets assigned top q.1 q.2.1 q.2.2)
      (P.assignedTopItem_assignment packets assigned top q.1 q.2.1 q.2.2)
  have hs := A.sum_referenceFamily_selected t (T top).slope (R top) cone w F
    hw hcone hF hwide hfrequency Finset.univ (A.crossPacketValue a ha t
      (fun j l => b j l.val.2) v f z) hcond
  simp only [Finset.mem_univ,Finset.filter_true] at hs
  have hterm (q : (Q top).PacketIndex) :
      (Q top).physicalCrossPacketValue (alts top) (halt top) (T top).slope
        (fun j l => b j (orig top j l)) v f 0 z q =
      A.crossPacketValue a ha t (fun j l => b j l.val.2) v f z
        ⟨q.1,A.referenceOriginalLabel t (T top).slope (R top) cone w q.1 q.2.1,q.2.2⟩ := by
    exact A.referenceFamily_crossPacketValue t (T top).slope (R top) cone w F
      hw hcone hF hwide hfrequency a ha (fun j l => b j l.val.2) v f q.1 q.2.1 q.2.2 z
  have hcoeff : (Q top).physicalMultiplierCoefficient (T top).slope
      (fun j l => b j (orig top j l)) v f =
      (fun j l u => P.physicalMultiplierCoefficient t b v f j (orig top j l) u.val) := by
    funext j l u
    exact P.assignedTopReference_physicalMultiplierCoefficient packets assigned top t
      (T top).slope (R top) cone w F hw hcone hF hwide hfrequency b v f j l u
  calc
    _ = ∑ q : A.PacketIndex, A.crossPacketValue a ha t (fun j l => b j l.val.2) v f z q :=
      (P.sum_assignedTopPackets packets assigned top (P.crossPacketValue alt hAlt t b v f z)).symm
    _ = ∑ q : (Q top).PacketIndex,
        (Q top).physicalCrossPacketValue (alts top) (halt top) (T top).slope
          (fun j l => b j (orig top j l)) v f 0 z q := by
      rw [←hs]
      exact Finset.sum_congr rfl (fun q _ => (hterm q).symm)
    _ = _ := by
      rw [(Q top).crossSum_eq_rawInterval,hcoeff]

omit R cone w F hw hcone hF hwide hfrequency in
 theorem sum_assignedPhysicalMaskedValue (tops : Finset τ)
    (hassigned : ∀ q∈packets, assigned q∈tops) (L A : ℝ) (z : ℝ×ℝ) :
    (∑ q∈packets, P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q) =
    ∑ top∈tops, (T top).mask L A z •
      ∑ q∈packets.filter (fun q => assigned q=top), P.crossPacketValue alt hAlt t b v f z q := by
  rw [←Finset.sum_fiberwise_of_maps_to hassigned]
  apply Finset.sum_congr rfl
  intro top _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hqt := (Finset.mem_filter.mp hq).2
  rw [P.physicalMaskedValue_eq_cross_at alt hAlt t b v f]
  simp only [hqt]

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskIntegral
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source-normalized mask error. The weak count is derived from
the actual popular witnesses, and the area relation removes its square
root factors. The mask scale is fixed before all finite families. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert

theorem source_mask_integral (hLL : LaceyLiInput) (C H a aw s d : ℝ)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (haw : 0 ≤ aw) (hs : 0 ≤ s) (hd : 4 ≤ d) :
    ∃ A L0 : ℝ, a < A ∧ 2 < A ∧ 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
        (T : ι → SlopeBox) (l r : ℝ), (∀ i, |(T i).slope| ≤ 1) →
      ∀ (u : Plane → ℝ) (lip : ℝ≥0), LipschitzWith lip u →
      300*((2*lip:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ E : ι → Set (ℝ × ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ (T i).radius z ≤ L^aw) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal (L^(-aw)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) → 0 < ∑ i, (T i).area →
      ∀ (ratio : ℝ) (F G : Set (ℝ × ℝ)), 0 ≤ ratio →
      (volume.prod volume) F ≠ ∞ → MeasurableSet G → G ⊆ F →
      (∀ z ∈ G, z.1 ∈ Icc l r) →
      (∑ i, (T i).area) ≤ L^s*ratio^2*(volume.prod volume).real F →
      ∀ V : ι → ℝ × ℝ → EuclideanSpace ℂ κ, (∀ i, Measurable (V i)) →
      (∀ᵐ z ∂(volume.prod volume).restrict G, ∀ i,
        ‖V i z‖ ≤ L^C*((T i).weight (L^a) d z)^8) →
      IntegrableOn (fun z => ‖(∑ i, V i z)-(∑ i, (T i).mask L A z • V i z)‖) G
        (volume.prod volume) ∧
      (∫ z in G, ‖(∑ i, V i z)-(∑ i, (T i).mask L A z • V i z)‖ ∂volume.prod volume) ≤
        L^(-H)*ratio*(volume.prod volume).real F := by
  obtain ⟨Cc,hCc,hcount⟩ := popular_top_count_powers hLL aw a d haw hd
  let e := aw+3*max a aw
  have he : 0 ≤ e := by dsimp [e]; linarith [le_max_right a aw]
  obtain ⟨A,Lm,haA,hA,hLm,hmask⟩ := exists_slope_mask_integral_above C (H+e+s/2+2) a d a
    hC (by positivity) (by linarith)
  refine ⟨A,max Lm (max 1 (2*Cc)),haA,hA,hLm.trans (le_max_left _ _),?_⟩
  intro L hL ι κ _ _ T l r hslopes u lip hu hlength E hE hdisj hinside hclose hsize hSpos
    ratio F G hratio hFfin hG hGF hGstrip hS V hV hpoint
  have hLmL : Lm ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hCcL : 2*Cc ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hCcL2 : 2*Cc ≤ L^2 := hCcL.trans (by nlinarith)
  have hGfin : (volume.prod volume) G ≠ ∞ := ne_top_of_le_ne_top hFfin (measure_mono hGF)
  by_cases hGzero : (volume.prod volume) G = 0
  · simp only [IntegrableOn, Measure.restrict_eq_zero.mpr hGzero, integrable_zero_measure,
      integral_zero_measure, true_and]
    positivity
  let μ := (volume.prod volume).restrict G
  let B := Cc*L^e*Real.sqrt (∑ i, (T i).area)
  have hB : 0 < B := mul_pos (mul_pos hCc (Real.rpow_pos_of_pos hLpos _))
    (Real.sqrt_pos.mpr hSpos)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hGfin
  have hμ : μ univ ≠ 0 := by simpa only [μ, Measure.restrict_apply_univ] using hGzero
  have hweak (t : ℝ) (ht : 0 < t) :
      μ {z | t < ∑ i, (T i).weight (L^a) d z} ≤ ENNReal.ofReal (B^2/t^2) := by
    have hm : Measurable (fun z => ∑ i, (T i).weight (L^a) d z) :=
      Finset.measurable_sum _ (fun i _ =>
        ((T i).weight_continuous _ d (Real.rpow_pos_of_pos hLpos _)).measurable)
    change ((volume.prod volume).restrict G) _ ≤ _
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hm)]
    apply (measure_mono (show {z | t < ∑ i, (T i).weight (L^a) d z} ∩ G ⊆
      {z | z.1 ∈ Icc l r} ∩ {z | t < ∑ i, (T i).weight (L^a) d z} from
        fun z hz => ⟨hGstrip z hz.2,hz.1⟩)).trans
    exact hcount L hL1 ι T l r hslopes u lip hu hlength E hE hdisj hinside hclose hsize t ht
  obtain ⟨hint,hintbound⟩ := hmask L hLmL ι κ μ hμ T V hV hpoint B hB hweak
  refine ⟨hint,?_⟩
  have hnorm := mask_error_normalization L Cc e s H ratio
    ((volume.prod volume).real F) ((volume.prod volume).real G) (∑ i, (T i).area)
    hLpos hCc.le hCcL2 hratio measureReal_nonneg
    (measureReal_mono hGF hFfin) hS
  apply le_trans ?_ hnorm
  simpa only [μ, Measure.restrict_apply_univ, B, Measure.real] using hintbound

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedMaskRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mask removal for the literal assigned original packet sum. The
per-top raw concentration bound is used with the unchanged original
analyzing coefficients, after exact finite regrouping. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_assigned_mask_removal (hLL : LaceyLiInput) (C H a aw s d : ℝ)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (haw : 0 ≤ aw) (hs : 0 ≤ s) (hd : 4 ≤ d) :
    ∃ A L0 : ℝ, a < A ∧ 2 < A ∧ 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w Freq : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hFreq : 0 ≤ Freq) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ Freq/w)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
      (f : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ q ∈ packets, P.referenceCondition oldSlope (T (assigned q)).slope
        (R (assigned q)) cone w q.1 q.2.1) →
    ∀ l r : ℝ, (∀ i, |(T i).slope| ≤ 1) →
    ∀ (u : Plane → ℝ) (lip : ℝ≥0), LipschitzWith lip u →
      300*((2*lip:ℝ≥0):ℝ)*(r-l) ≤ 1 →
    ∀ E : τ → Set (ℝ×ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ (T i).radius z ≤ L^aw) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal (L^(-aw)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) → 0 < ∑ i, (T i).area →
    ∀ (ratio : ℝ) (F G : Set (ℝ×ℝ)), 0 ≤ ratio →
      (volume.prod volume) F ≠ ∞ → MeasurableSet G → G ⊆ F →
      (∀ z ∈ G, z.1 ∈ Icc l r) →
      (∑ i, (T i).area) ≤ L^s*ratio^2*(volume.prod volume).real F →
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency alt hAlt
    (∀ z ∈ G, ∀ top,
      ‖((Q top).withProfile (alts top) (halt top)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
        0 0 N z.1 (z.2-(T top).slope*z.1)‖ ≤ L^C*((T top).weight (L^a) d z)^8) →
    let original := fun z => ∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q
    let masked := fun z => ∑ q ∈ packets, P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q
    IntegrableOn (fun z => ‖original z-masked z‖) G (volume.prod volume) ∧
      (∫ z in G, ‖original z-masked z‖ ∂volume.prod volume) ≤
        L^(-H)*ratio*(volume.prod volume).real F := by
  obtain ⟨A,L0,haA,hA,hL0,hmask⟩ := source_mask_integral hLL C H a aw s d hC hH haw hs hd
  refine ⟨A,L0,haA,hA,hL0,?_⟩
  intro L hL τ κ _ _ N Label Item _ P packets assigned T oldSlope R cone w Freq
    hw hcone hFreq hwide hfrequency alt hAlt b v f hcondition l r hslopes u lip hu hlength
    E hE hdisj hinside hclose hsize hSpos ratio F G hratio hFfin hG hGF hstrip hS
    Q orig alts halt hraw original masked
  let V := fun top z => ∑ q ∈ packets.filter (fun q => assigned q = top),
    P.crossPacketValue alt hAlt oldSlope b v f z q
  have hV (top : τ) : Measurable (V top) := by
    apply Continuous.measurable
    exact continuous_finsetSum _ (fun q _ => P.crossPacketValue_continuous alt hAlt oldSlope b v f q)
  have hpoint : ∀ᵐ z ∂(volume.prod volume).restrict G, ∀ top,
      ‖V top z‖ ≤ L^C*((T top).weight (L^a) d z)^8 := by
    filter_upwards [ae_restrict_mem hG] with z hz
    intro top
    dsimp only [V]
    rw [P.assignedCrossSum_eq_rawInterval alt hAlt oldSlope b v f packets assigned T R cone w Freq
      hw hcone hFreq hwide hfrequency z top (fun q hq hqt => by
        simpa only [hqt] using hcondition q hq)]
    exact hraw z hz top
  have hm := hmask L hL τ κ T l r hslopes u lip hu hlength E hE hdisj hinside hclose
    hsize hSpos ratio F G hratio hFfin hG hGF hstrip hS V hV hpoint
  have horig (z : ℝ×ℝ) : (∑ top, V top z) = original z := by
    exact Finset.sum_fiberwise_of_maps_to (fun q _ => Finset.mem_univ (assigned q))
      (fun q => P.crossPacketValue alt hAlt oldSlope b v f z q)
  have hmasked (z : ℝ×ℝ) : (∑ top, (T top).mask L A z • V top z) = masked z := by
    exact (P.sum_assignedPhysicalMaskedValue alt hAlt oldSlope b v f packets assigned T
      Finset.univ (fun q _ => Finset.mem_univ (assigned q)) L A z).symm
  simpa only [horig,hmasked] using hm

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedSelectorGoodSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One fixed testing subset for the original selector coefficients.
The mask exponent is chosen before the larger counting dilation. Actual
concentration, smooth-count cutoff and mask removal all hold on this set. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_assigned_selector_mask_good_set_oai (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb)
    (aWeight aw p s Hloss Lip : ℝ) (D K H J₀ : ℕ)
    (haWeight : 0 ≤ aWeight) (haw : 0 ≤ aw) (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hHloss : 0 ≤ Hloss) (hLip : 0 ≤ Lip) (hD : 4 ≤ D) :
    ∃ A Cn L0 : ℝ, aWeight < A ∧ 2 < A ∧ 0 < Cn ∧ 2 ≤ L0 ∧
    ∀ L : ℝ, L0 ≤ L →
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      P.referenceEnvelopeConstant ≤ L^p → 6+2*(8*D+1) ≤ P.order →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k,
        planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ top, P.width ≤ L^aWeight*(T top).width) →
      (∀ top, P.scale = 4*(L^aWeight*(T top).width)) →
      (∀ q ∈ packets,
        |P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x|+P.length q.1 ≤
          L^aWeight*(T (assigned q)).length) →
      (∀ q ∈ packets,
        |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(T (assigned q)).slope)*
          P.actualX q.1 q.2.1 q.2.2-
          ((T (assigned q)).y-(T (assigned q)).slope*(T (assigned q)).x)|+P.width ≤
            L^aWeight*(T (assigned q)).width) →
    ∀ (angle : τ → ℝ) (small wide radius : ℝ) (E J : ℕ),
      (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
      wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
      (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => oldSlope+P.rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) →
      (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
        ‖b j l k s-b j l k (T top).slope‖ ≤
          Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
        b j l k s = 0) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f →
      (∀ z, ‖f z‖ ≤ 1) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket
          oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (∃ k, b j l k (T top).slope ≠ 0) →
        cb*w/P.length j ≤ |oldSlope+P.rowSlope j l-(T top).slope| ∧
          |oldSlope+P.rowSlope j l-(T top).slope| ≤ Cb*w/P.length j) →
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
      (∀ q ∈ packets, P.referenceCondition oldSlope (T (assigned q)).slope
        (R (assigned q)) cone w q.1 q.2.1) →
    ∀ l r : ℝ, (∀ i, |(T i).slope| ≤ 1) →
    ∀ (u : Plane → ℝ) (lip : ℝ≥0), LipschitzWith lip u →
      300*((2*lip:ℝ≥0):ℝ)*(r-l) ≤ 1 →
    ∀ witness : τ → Set (ℝ×ℝ), (∀ i, MeasurableSet (witness i)) →
      (Pairwise fun i j => Disjoint (witness i) (witness j)) →
      (∀ i z, z ∈ witness i → z.1 ∈ Icc l r ∧ (T i).radius z ≤ L^aw) →
      (∀ i z, z ∈ witness i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal (L^(-aw)*(T i).length*(T i).width) ≤
        (volume.prod volume) (witness i)) → 0 < ∑ i, (T i).area →
    ∀ (ratio : ℝ) (Fset : Set (ℝ×ℝ)), 0 < ratio → MeasurableSet Fset →
      (volume.prod volume) Fset ≠ ∞ →
      (∀ z ∈ Fset, z.1 ∈ Icc l r) → ratio ≤ Real.exp (2*L) →
      (∑ i, (T i).area) ≤ L^s*ratio^2*(volume.prod volume).real Fset →
      let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
        oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      let orig := fun top j (l : (Q top).labels j) =>
        ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
          oldSlope (T top).slope (R top) cone w j l).val.2
      let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        alt j (orig top j l) u.val k
      let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        hAlt j (orig top j l) u.val k
      ∃ G : Set (ℝ×ℝ), MeasurableSet G ∧ G ⊆ Fset ∧
        (volume.prod volume) (Fset\G) ≤ ENNReal.ofReal (L^(-Hloss)*(volume.prod volume).real Fset) ∧
        (∀ z ∈ G, (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z) ≤ ratio*L^Cn) ∧
        (∀ top lower upper, lower ≤ upper → upper ≤ N → ∀ z ∈ G, ∀ yy,
          |yy-(z.2-(T top).slope*z.1)| ≤ (T top).width →
          let V := ((Q top).withProfile (a top) (ha top)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
            0 lower upper
          ‖V z.1 yy‖+(T top).width*‖covariantSignal P.frequency
            (fun k y => V z.1 y k) yy‖ ≤ L^(2*p+8)*((T top).weight (L^aWeight) (D:ℝ) z)^8) ∧
        let original := fun z => ∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q
        let masked := fun z => ∑ q ∈ packets, P.physicalMaskedValue alt hAlt oldSlope b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q
        IntegrableOn (fun z => ‖original z-masked z‖) G (volume.prod volume) ∧
        (∫ z in G, ‖original z-masked z‖ ∂volume.prod volume) ≤
          L^(-Hloss)*ratio*(volume.prod volume).real Fset := by
  obtain ⟨A,Lmask,haA,hA,hLmask,hmask⟩ := source_assigned_mask_removal hLL
    (2*p+8) Hloss aWeight aw s (D:ℝ) (by linarith) hHloss haw hs (by exact_mod_cast hD)
  obtain ⟨Cn,Lcount,hCn,hLcount,hcount⟩ := popular_top_count_discard hLL aw (A+2)
    (D:ℝ) s (Hloss+1) haw (by exact_mod_cast hD) hs (by linarith)
  obtain ⟨Lconc,hLconc⟩ := eventually_atTop.mp
    (eventually_assigned_top_selector_concentration_of_supported hVariation
      cStar cEta CEta cb Cb F hcStar hcEta hCEta hcb hCb hF hgap
      10 aWeight p Lip D K H J₀ (by norm_num) haWeight hp hLip)
  obtain ⟨Larea,hLarea⟩ := eventually_atTop.mp (eventually_top_area_factor s (Hloss+1))
  let L0 := max 2 (max Lmask (max Lcount (max Lconc Larea)))
  refine ⟨A,Cn,L0,haA,hA,hCn,le_max_left _ _,?_⟩
  intro L hL τ κ _ _ N Label Item _ P packets assigned hP horder alt hAlt T oldSlope R cone w
    hw hcone hwide hfrequency hwidth hscale hX hZ angle small wide radius E J
    hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal b hb hb1 hsupport hnear hfar
    v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE hcondition l r hslopes u lip hu hlength
    witness hW hdisj hinside hclose hsize hSpos ratio Fset hratio hFset hFfinite hFstrip hNupper hS
    Q orig a ha
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := by linarith
  have hLm : Lmask ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLc : Lcount ≤ L := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLt : Lconc ≤ L := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL)))
  have hLa : Larea ≤ L := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL)))
  obtain ⟨bad,hbad,hbadArea,hpoint⟩ := hLconc L hLt τ κ N Label Item P packets assigned hP horder
    alt hAlt T oldSlope R cone w hw hcone hwide hfrequency hwidth hscale hX hZ
    angle small wide radius E J hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal
    b hb hb1 hsupport hnear hfar v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE
  let count := fun z => ∑ i, (T i).weight (L^(A+2)) (D:ℝ) z
  let tail := {z | ratio*L^Cn < count z}
  have htail : MeasurableSet tail := measurableSet_lt measurable_const
    (Finset.measurable_sum _ (fun i _ => ((T i).continuous_weight
      (Real.rpow_pos_of_pos hLpos _) _).measurable))
  let G := Fset \ (bad ∪ tail)
  have hG : MeasurableSet G := hFset.diff (hbad.union htail)
  have hGF : G ⊆ Fset := sdiff_subset
  have hgBad {z : ℝ×ℝ} (hz : z ∈ G) : z ∉ bad := fun hb => hz.2 (Or.inl hb)
  have hraw top lower upper (hlu : lower ≤ upper) (hup : upper ≤ N) z (hz : z ∈ G) yy
      (hy : |yy-(z.2-(T top).slope*z.1)| ≤ (T top).width) :
      let V := ((Q top).withProfile (a top) (ha top)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
        0 lower upper
      ‖V z.1 yy‖+(T top).width*‖covariantSignal P.frequency
        (fun k y => V z.1 y k) yy‖ ≤ L^(2*p+8)*((T top).weight (L^aWeight) (D:ℝ) z)^8 := by
    have hh := hpoint top lower upper hlu hup z (yy-(z.2-(T top).slope*z.1)) hy (hgBad hz)
    have he : z.2-(T top).slope*z.1+(yy-(z.2-(T top).slope*z.1)) = yy := by ring
    simpa only [he] using hh
  have hcountArea := hcount L hLc τ T l r hslopes u lip hu hlength witness hW hdisj
    hinside hclose hsize ratio Fset hratio hFstrip hS
  have hbArea : (volume.prod volume) bad ≤ ENNReal.ofReal
      (L^(-(Hloss+1))*(volume.prod volume).real Fset) := by
    apply hbadArea.trans
    apply ENNReal.ofReal_le_ofReal
    have hnum := top_area_discard_numeric L s (Hloss+1) ratio ((volume.prod volume).real Fset)
      (∑ i, (T i).area) hLpos hratio.le measureReal_nonneg hNupper hS (hLarea L hLa)
    have hn : 0 ≤ L^(-(Hloss+1))*(volume.prod volume).real Fset :=
      mul_nonneg (Real.rpow_nonneg hLpos.le _) measureReal_nonneg
    exact hnum.trans (by nlinarith)
  have harea : (volume.prod volume) (Fset\G) ≤
      ENNReal.ofReal (L^(-Hloss)*(volume.prod volume).real Fset) := by
    have hsub : Fset\G ⊆ bad ∪ (Fset ∩ tail) := by
      intro z hz
      have hh : z ∈ bad ∪ tail := by
        by_contra hn
        exact hz.2 ⟨hz.1,hn⟩
      rcases hh with hb | ht
      · exact Or.inl hb
      · exact Or.inr ⟨hz.1,ht⟩
    have hpower : 2*L^(-(Hloss+1)) ≤ L^(-Hloss) := by
      have hi : L⁻¹ ≤ (1/2:ℝ) := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hL2
      rw [show L^(-(Hloss+1)) = L^(-Hloss)*L⁻¹ by
        rw [← Real.rpow_neg_one,← Real.rpow_add hLpos]; congr 1; ring]
      nlinarith [Real.rpow_nonneg hLpos.le (-Hloss)]
    calc
      _ ≤ (volume.prod volume) bad+(volume.prod volume) (Fset ∩ tail) :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (L^(-(Hloss+1))*(volume.prod volume).real Fset)+
          ENNReal.ofReal (L^(-(Hloss+1))*(volume.prod volume).real Fset) := add_le_add hbArea hcountArea
      _ ≤ _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_le_mul_of_nonneg_right hpower (measureReal_nonneg (μ := volume.prod volume) (s := Fset))]
  refine ⟨G,hG,hGF,harea,?_,?_,?_⟩
  · intro z hz
    exact le_of_not_gt (fun ht => hz.2 (Or.inr ht))
  · exact hraw
  · apply hmask L hLm τ κ N Label Item P packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v f hcondition l r hslopes u lip hu hlength
      witness hW hdisj hinside hclose hsize hSpos ratio Fset G hratio.le hFfinite hG hGF
      (fun z hz => hFstrip z (hGF hz)) hS
    intro z hz top
    have hh := hraw top 0 N (Nat.zero_le _) le_rfl z hz (z.2-(T top).slope*z.1)
      (by simpa only [sub_self,abs_zero] using (T top).width_pos.le)
    exact (le_add_of_nonneg_right (mul_nonneg (T top).width_pos.le (norm_nonneg _))).trans hh

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketLatticeData.source_assigned_selector_mask_good_set_oai := @OAI.LipschitzHilbert.PacketLatticeData.source_assigned_selector_mask_good_set_oai
