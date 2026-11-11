-- Prove2me | solution 1 for OAI.MetricKMedian.GraphComparison.normalized_drift_le_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:14:26.892735+00:00
-- url     : https://prove2.me/submissions/aef8d417-abe9-405d-8c9f-573982f80473

import Mathlib
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K029
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_le_half_s35
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_nonneg_s35
import Theorems.Thm_OAI_MetricKMedian_FiniteComparison_actual_scalar_bounds_s35
import Theorems.Thm_OAI_MetricKMedian_FiniteComparison_finite_charge_s35

section
-- module Solutions.Q224_RR.KMedian_Analysis_FiniteAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FiniteComparison

theorem average_mono {I : Type*} [Fintype I] {π f h : I → ℝ}
    (hπ : ∀ i, 0 ≤ π i) (hfh : ∀ i, f i ≤ h i) : average π f ≤ average π h := by
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hfh i) (hπ i))

theorem average_nonneg {I : Type*} [Fintype I] {π f : I → ℝ}
    (hπ : ∀ i, 0 ≤ π i) (hf : ∀ i, 0 ≤ f i) : 0 ≤ average π f := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hπ i) (hf i))

theorem average_const {I : Type*} [Fintype I] {π : I → ℝ}
    (hπ : ∑ i, π i = 1) (c : ℝ) : average π (fun _ => c) = c := by
  simp only [average, ← Finset.sum_mul, hπ, one_mul]

theorem average_add {I : Type*} [Fintype I] (π f h : I → ℝ) :
    average π (fun i => f i + h i) = average π f + average π h := by
  simp only [average, mul_add, Finset.sum_add_distrib]

theorem average_sub {I : Type*} [Fintype I] (π f h : I → ℝ) :
    average π (fun i => f i - h i) = average π f - average π h := by
  simp only [average, mul_sub, Finset.sum_sub_distrib]

theorem average_mul {I : Type*} [Fintype I] (π f : I → ℝ) (c : ℝ) :
    average π (fun i => c * f i) = c * average π f := by
  simp only [average, ← Finset.mul_sum, mul_left_comm]

theorem average_mul_right {I : Type*} [Fintype I] (π f : I → ℝ) (c : ℝ) :
    average π (fun i => f i * c) = average π f * c := by
  simp only [average, Finset.sum_mul, mul_assoc]

end MetricKMedian.FiniteComparison


end
end

end OAI
end

section
-- module Solutions.Q224_RR.KMedian_Analysis_RowComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FiniteComparison

theorem rawRow_affine {I : Type*} [Fintype I] (π Z q : I → ℝ)
    (p m y s D R : ℝ) : rawRow π Z q p m y s D R =
      (1 - s) * rawRow π Z q p m y 0 D R + s * rawRow π Z q p m y 1 D R := by
  unfold rawRow
  ring

theorem affine_le_max {u v s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * u + s * v ≤ max u v := by
  have h₁ := mul_le_mul_of_nonneg_left (le_max_left u v) (sub_nonneg.mpr hs1)
  have h₂ := mul_le_mul_of_nonneg_left (le_max_right u v) hs0
  nlinarith only [h₁, h₂]

theorem rawRow_mono_y {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m y y' s D R : ℝ} (hπ0 : ∀ t, 0 ≤ π t) (hp : 0 ≤ p)
    (hD : 0 ≤ D) (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1)
    (hs : s ≤ 1) (hy : y ≤ y') : rawRow π Z q p m y s D R ≤ rawRow π Z q p m y' s D R := by
  have hr := average_nonneg hπ0 hq0
  have hlin := mul_le_mul_of_nonneg_left hy
    (mul_nonneg (mul_nonneg (mul_nonneg hr (by linarith : 0 ≤ 2 - s)) hp)
      (by linarith : 0 ≤ D + 1))
  have hhinge : average π (fun t => (1 - q t) * max (Z t - (1 + m + 2 * p * y') * D) 0) ≤
      average π (fun t => (1 - q t) * max (Z t - (1 + m + 2 * p * y) * D) 0) := by
    apply average_mono hπ0
    intro t
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (hq t))
    apply max_le_max_right
    have ht := mul_le_mul_of_nonneg_left hy (mul_nonneg (by positivity : 0 ≤ 2 * p) hD)
    nlinarith only [ht]
  unfold rawRow
  nlinarith only [hlin, hhinge]

theorem rawRow_eq_rowValue {I : Type*} [Fintype I] (π Z q : I → ℝ)
    (p m y z D R : ℝ) (s : Bool) :
    rawRow π Z q p m y (endpoint s) D R =
      rowValue π Z q p m (1 + m + 2 * p * y) z
        (fun s => (2 - endpoint s) * p * y) s D R + ((2 / 5) * D + 8 / 5) * z := by
  cases s <;> simp only [rawRow, rowValue, C, endpoint, Bool.false_eq_true, ↓reduceIte] <;> ring

theorem finite_raw_of_scalar {I : Type*} [Fintype I] {π D R : I → ℝ}
    {q : I → I → ℝ} {s : I → ℝ} {p m y z h : ℝ}
    (sb : ScalarBounds p m (1 + m + 2 * p * y) z h (fun s => (2 - endpoint s) * p * y))
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (hD0 : ∀ i, 0 ≤ D i) (hD : average π D = 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → R i * (1 - p * q i t) ≤ D i + D t) :
    average π (fun i => rawRow π D (q i) p m y (s i) (D i) (R i)) ≤ 2 * z := by
  classical
  let v : I → Bool := fun i => decide
    (rawRow π D (q i) p m y 0 (D i) (R i) ≤ rawRow π D (q i) p m y 1 (D i) (R i))
  have hpoint : ∀ i, rawRow π D (q i) p m y (s i) (D i) (R i) ≤
      rawRow π D (q i) p m y (endpoint (v i)) (D i) (R i) := by
    intro i
    rw [rawRow_affine]
    have he := affine_le_max (u := rawRow π D (q i) p m y 0 (D i) (R i))
      (v := rawRow π D (q i) p m y 1 (D i) (R i)) (hs0 i) (hs i)
    by_cases hle : rawRow π D (q i) p m y 0 (D i) (R i) ≤ rawRow π D (q i) p m y 1 (D i) (R i)
    · simpa only [v, hle, decide_true, endpoint, ↓reduceIte, max_eq_right hle] using he
    · simpa only [v, hle, decide_false, endpoint, Bool.false_eq_true, ↓reduceIte,
        max_eq_left (le_of_not_ge hle)] using he
  have hcharge := finite_charge_s35 (s := v) sb hπ0 hπ hD0 hD hq0 hq hcomp
  have hav := average_mono hπ0 hpoint
  simp only [rawRow_eq_rowValue (z := z), average_add, average_mul_right,
    average_mul, average_const hπ, hD] at hav
  linarith

end MetricKMedian.FiniteComparison


end
end

end OAI
end

section
-- module Solutions.Q224_RR.KMedian_Analysis_FiniteComparison
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

open Analytic

theorem finite_comparison {I : Type*} [Fintype I] {π D R : I → ℝ}
    {q : I → I → ℝ} {s : I → ℝ} {x y : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 < y) (hy : y ≤ 1)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (hD0 : ∀ i, 0 ≤ D i) (hD : average π D = 1) (_hR0 : ∀ i, 0 ≤ R i)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → R i*(1-P x*q i t) ≤ D i+D t) :
    average π (fun i => rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)) ≤
      2*(P x*(y-x)^2/y) := by
  let w := max 0 (y-x)
  have hw0 : 0 ≤ w := le_max_left _ _
  have hw : w ≤ 1-x := max_le (by linarith) (by linarith)
  have hyy : y ≤ x+w := by have h := le_max_right 0 (y-x); dsimp [w] <;> linarith
  have ha : A x+2*P x*w = 1+m x+2*P x*(x+w) := by unfold m; ring
  have hbs : actualB x w = fun s => (2-endpoint s)*P x*(x+w) := rfl
  have sb := actual_scalar_bounds_s35 hx0 hx hw0 hw
  rw [ha, hbs] at sb
  have hfinite := finite_raw_of_scalar sb hπ0 hπ hD0 hD hq0 hq hs0 hs hcomp
  have hmono : average π (fun i => rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)) ≤
      average π (fun i => rawRow π D (q i) (P x) (m x) (x+w) (s i) (D i) (R i)) := by
    apply average_mono hπ0
    intro i
    exact rawRow_mono_y hπ0 (P_nonneg_s35 x) (hD0 i) (hq0 i) (hq i) (hs i) hyy
  have hz : P x*w^2 ≤ P x*(y-x)^2/y := by
    rcases le_total y x with h | h
    · have hwz : w = 0 := max_eq_left (sub_nonpos.mpr h)
      rw [hwz]
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero]
      exact div_nonneg (mul_nonneg (P_nonneg_s35 x) (sq_nonneg _)) hy0.le
    · have hwe : w = y-x := max_eq_right (sub_nonneg.mpr h)
      rw [hwe]
      exact (le_div_iff₀ hy0).mpr
        (mul_le_of_le_one_right (mul_nonneg (P_nonneg_s35 x) (sq_nonneg _)) hy)
  exact hmono.trans (hfinite.trans (mul_le_mul_of_nonneg_left hz (by norm_num)))

end MetricKMedian.FiniteComparison

end
end

end OAI
end

section
-- module Solutions.Q224_RR.KMedian_Geometry_GraphComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GraphComparison

open FiniteComparison Analytic

theorem kernel_average_bound {I : Type*} [Fintype I] {π D s r : I → ℝ} {K : I → I → ℝ} {y : ℝ}
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i=1) (hD0 : ∀ i, 0 ≤ D i) (hD : average π D=1)
    (hK : ∀ i t, K i t ≤ (s i*(1-y*r i)+s t*(1-y*r t))/2) :
    2*average π (fun i => average π (fun t => K i t*D t)) ≤
      average π (fun i => s i*(1-y*r i)*(1+D i)) := by
  have hb := average_mono hπ0 (fun i => average_mono hπ0
    (fun t => mul_le_mul_of_nonneg_right (hK i t) (hD0 t)))
  have hid : average π (fun i => average π (fun t =>
      ((s i*(1-y*r i)+s t*(1-y*r t))/2)*D t)) =
      (1/2)*average π (fun i => s i*(1-y*r i)*(1+D i)) := by
    have hpoint : ∀ i t, ((s i*(1-y*r i)+s t*(1-y*r t))/2)*D t =
        (1/2)*(s i*(1-y*r i))*D t+(1/2)*(s t*(1-y*r t)*D t) := by intros; ring
    simp_rw [hpoint, average_add, average_mul, hD, mul_one, average_const hπ]
    rw [average_mul, ←mul_add, ←average_add]
    congr 2
    funext i
    ring
  rw [hid] at hb
  linarith only [hb]

theorem taper_error {p pHat ζ u : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hζ0 : 0 ≤ ζ) (he : |pHat-p| ≤ ζ) (hu0 : 0 ≤ u) (hu : u ≤ 1) :
    0 ≤ (1-pHat*u)-(1-2*ζ)*(1-p*u) ∧
      (1-pHat*u)-(1-2*ζ)*(1-p*u) ≤ 3*ζ := by
  have hehe := abs_le.mp he
  have huζ := mul_le_mul_of_nonneg_left hu hζ0
  have hupper := mul_le_mul_of_nonneg_right hehe.1 hu0
  have hlower := mul_le_mul_of_nonneg_right hehe.2 hu0
  have hpu := mul_le_mul hp hu hu0 (by norm_num : (0:ℝ) ≤ 1/2)
  have hpu0 := mul_nonneg hp0 hu0
  have hpuz := mul_le_mul_of_nonneg_left hpu hζ0
  have hpuz0 := mul_nonneg hζ0 hpu0
  constructor <;> nlinarith only [huζ, hupper, hlower, hpuz, hpuz0]

theorem radius_control {I : Type*} [Fintype I] {π D : I → ℝ} {q : I → I → ℝ}
    {N : I → ℝ} {pHat : ℝ}
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i=1) (hD0 : ∀ i, 0 ≤ D i) (hD : average π D=1)
    (hN0 : ∀ i, 0 ≤ N i) (_hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ D i+D t) (i : I) :
    (1-average π (q i))*N i ≤ 2*(D i+1) := by
  have hpoint : ∀ t, (1-q i t)*N i ≤ 2*(D i+D t) := by
    intro t
    rcases eq_or_lt_of_le (hq i t) with heq | hlt
    · rw [heq]
      have hpos := add_nonneg (hD0 i) (hD0 t)
      nlinarith
    · have hh := hcomp i t hlt
      have hpq := mul_le_mul hp (hq i t) (hq0 i t) (by norm_num : (0:ℝ) ≤ 1/2)
      have hden : 1/2 ≤ 1-pHat*q i t := by linarith
      have hmul := mul_le_mul_of_nonneg_left hden (hN0 i)
      have hcut := mul_nonneg (hq0 i t) (hN0 i)
      nlinarith only [hh, hmul, hcut]
  have hb := average_mono hπ0 hpoint
  simp only [average_mul_right, average_sub, average_mul, average_add, average_const hπ, hD] at hb
  exact hb

theorem normalized_drift_le_s35_oai {I : Type*} [Fintype I]
    {π D N s : I → ℝ} {q K : I → I → ℝ} {x y pHat ζ : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 < y) (hy : y ≤ 1)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i=1)
    (hD0 : ∀ i, 0 ≤ D i) (hD : average π D=1) (hN : ∀ i, 0 ≤ N i)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
    (he : |pHat-P x| ≤ ζ)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ D i+D t)
    (hK : ∀ i t, K i t ≤
      (s i*(1-y*average π (q i))+s t*(1-y*average π (q t)))/2) :
    normalizedDrift π D N s q K x y pHat ≤ 12*ζ := by
  let R : I → ℝ := fun i => (1-2*ζ)*N i
  let err : I → ℝ := fun i => (1-average π (q i))*N i*
    ((1-pHat*s i)-(1-2*ζ)*(1-P x*s i))
  have hpP := P_le_half_s35 hx0
  have hpP0 := P_nonneg_s35 x
  have hR : ∀ i, 0 ≤ R i := by
    intro i
    exact mul_nonneg (by linarith only [hζ]) (hN i)
  have hcompR : ∀ i t, q i t < 1 → R i*(1-P x*q i t) ≤ D i+D t := by
    intro i t hit
    have ht := (taper_error hpP0 hpP hζ0 he (hq0 i t) (hq i t)).1
    have hm := mul_le_mul_of_nonneg_right (sub_nonneg.mp ht) (hN i)
    dsimp only [R]
    nlinarith only [hm, hcomp i t hit]
  have hfinite := finite_comparison hx0 hx hy0 hy hπ0 hπ hD0 hD hR
    hq0 hq hs0 hs hcompR
  have herr : ∀ i, err i ≤ 6*ζ*(D i+1) := by
    intro i
    have hr : average π (q i) ≤ 1 := by
      have hr := average_mono hπ0 (hq i)
      simpa only [average_const hπ] using hr
    have hn : 0 ≤ (1-average π (q i))*N i :=
      mul_nonneg (sub_nonneg.mpr hr) (hN i)
    have ht := (taper_error hpP0 hpP hζ0 he (hs0 i) (hs i)).2
    have hrad := radius_control hπ0 hπ hD0 hD hN hp0 hp hq0 hq hcomp i
    have h1 := mul_le_mul_of_nonneg_left ht hn
    have h2 := mul_le_mul_of_nonneg_left hrad (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hζ0)
    dsimp only [err]
    nlinarith only [h1, h2]
  have herrAvg : average π err ≤ 12*ζ := by
    have hh := average_mono hπ0 herr
    simp only [average_mul, average_add, hD, average_const hπ] at hh
    nlinarith only [hh]
  have hker := mul_le_mul_of_nonneg_left (kernel_average_bound hπ0 hπ hD0 hD hK) hpP0
  have hid : normalizedDrift π D N s q K x y pHat =
      average π (fun i => rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)) +
      average π err -2*(P x*(y-x)^2/y)+
      P x*(2*average π (fun i => average π (fun t => K i t*D t))-
        average π (fun i => s i*(1-y*average π (q i))*(1+D i))) := by
    have hrow : ∀ i,
        (1-average π (q i))*(D i+(1-pHat*s i)*N i)+
        (1+m x+2*P x*y)*average π (q i)*D i+2*P x*y*average π (q i)-
        average π (fun t => (1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0) =
        rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)+err i+
        2*D i+1-P x*(s i*(1-y*average π (q i))*(1+D i)) := by
      intro i
      unfold rawRow
      dsimp only [R, err]
      ring
    unfold normalizedDrift
    have heq : ∀ i,
        (1-average π (q i))*(D i+(1-pHat*s i)*N i)+
        (1+m x+2*P x*y)*average π (q i)*D i+2*P x*y*average π (q i)+
        2*P x*average π (fun t => K i t*D t)-
        average π (fun t => (1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0) =
        (rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)+err i+
        2*D i+1-P x*(s i*(1-y*average π (q i))*(1+D i)))+
        2*P x*average π (fun t => K i t*D t) := by
      intro i
      have hh := hrow i
      linarith only [hh]
    simp only [heq, average_add, average_sub, average_mul, hD, average_const hπ]
    ring
  rw [hid]
  nlinarith only [hfinite, herrAvg, hker]

end MetricKMedian.GraphComparison
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedian.GraphComparison.normalized_drift_le_s35_oai.{u_1} := @OAI.MetricKMedian.GraphComparison.normalized_drift_le_s35_oai.{u_1}
