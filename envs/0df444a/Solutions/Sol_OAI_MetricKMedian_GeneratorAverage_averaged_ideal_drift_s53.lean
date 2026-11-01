-- Prove2me | solution 1 for OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:15:00.381818+00:00
-- url     : https://prove2.me/submissions/d55f6ea2-ba60-44b6-8a27-93567a97de82

import Mathlib
import Definitions.Def_OAIQ053K020
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_le_half_s53
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_nonneg_s53
import Theorems.Thm_OAI_MetricKMedian_FiniteComparison_finite_comparison_s53
import Theorems.Thm_OAI_MetricKMedian_GeneratorAverage_expanded_bound_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_FiniteAverages
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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_GraphComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GraphComparison

open FiniteComparison Analytic

theorem external_bounds {I H : Type*} [Fintype H] {ρ : H → ℝ} {q : I → H → ℝ}
    (hρ : ∀ h, 0 ≤ ρ h) (hq0 : ∀ i h, 0 ≤ q i h) (hq : ∀ i h, q i h ≤ 1) (i : I) :
    0 ≤ externalSquare ρ q i ∧ externalSquare ρ q i ≤ externalMass ρ q i := by
  constructor
  · exact Finset.sum_nonneg (fun h _ => mul_nonneg (hρ h) (sq_nonneg _))
  · apply Finset.sum_le_sum
    intro h _
    apply mul_le_mul_of_nonneg_left _ (hρ h)
    nlinarith [hq0 i h, hq i h]

theorem row_type_bounds {I H : Type*} [Fintype H] {ρ : H → ℝ} {q : I → H → ℝ}
    (hρ : ∀ h, 0 ≤ ρ h) (hq0 : ∀ i h, 0 ≤ q i h) (hq : ∀ i h, q i h ≤ 1) (i : I) :
    0 ≤ rowType ρ q i ∧ rowType ρ q i ≤ 1 ∧
      rowType ρ q i*externalMass ρ q i=externalSquare ρ q i := by
  have hb := external_bounds hρ hq0 hq i
  have hm : 0 ≤ externalMass ρ q i := hb.1.trans hb.2
  by_cases hz : externalMass ρ q i=0
  · have hs : externalSquare ρ q i=0 := by linarith
    simp [rowType, hz, hs]
  · have hp : 0 < externalMass ρ q i := lt_of_le_of_ne hm (Ne.symm hz)
    exact ⟨div_nonneg hb.1 hm, (div_le_one hp).mpr hb.2, div_mul_cancel₀ _ hz⟩

theorem kernel_bound {I H : Type*} [Fintype H] {ρ : H → ℝ} {q : I → H → ℝ}
    (hρ : ∀ h, 0 ≤ ρ h) (i t : I) :
    kernel ρ q i t ≤ (externalSquare ρ q i+externalSquare ρ q t)/2 := by
  have hp : ∀ h, 2*(ρ h*q i h*q t h) ≤ ρ h*(q i h)^2+ρ h*(q t h)^2 := by
    intro h
    have hn := mul_nonneg (hρ h) (sq_nonneg (q i h-q t h))
    nlinarith only [hn]
  have hsum := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) => hp h)
  simp only [Finset.sum_add_distrib, ←Finset.mul_sum] at hsum
  unfold kernel externalSquare
  linarith only [hsum]

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

theorem normalized_drift_le {I : Type*} [Fintype I]
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
  have hpP := P_le_half_s53 hx0
  have hpP0 := P_nonneg_s53 x
  have hR : ∀ i, 0 ≤ R i := by
    intro i
    exact mul_nonneg (by linarith only [hζ]) (hN i)
  have hcompR : ∀ i t, q i t < 1 → R i*(1-P x*q i t) ≤ D i+D t := by
    intro i t hit
    have ht := (taper_error hpP0 hpP hζ0 he (hq0 i t) (hq i t)).1
    have hm := mul_le_mul_of_nonneg_right (sub_nonneg.mp ht) (hN i)
    dsimp only [R]
    nlinarith only [hm, hcomp i t hit]
  have hfinite := finite_comparison_s53 hx0 hx hy0 hy hπ0 hπ hD0 hD hR
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

section
-- module Solutions.OAIQ053_KM.KMedian_Process_AveragedDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GraphComparison

open FiniteComparison Analytic

theorem cap_average {H : Type*} [Fintype H] {ρ q bH : H → ℝ}
    {b d N pHat y w s : ℝ}
    (hρ : ∀ h, 0 ≤ ρ h) (hq : ∀ h, 0 ≤ q h)
    (hw : w ≤ y) (hy : y ≤ 1)
    (hm : ∑ h, ρ h*q h=1-w)
    (hs : ∑ h, ρ h*(q h)^2=s*(1-w))
    (hb : ∀ h, bH h ≤ b)
    (htaper : ∀ h, 0 < q h → bH h ≤ d+(1-pHat*q h)*N) :
    (∑ h, ρ h*q h*bH h) ≤ (1-y)*b+(y-w)*(d+(1-pHat*s)*N) := by
  let F := ∑ h, ρ h*q h*bH h
  have hfirst : F ≤ (1-w)*b := by
    rw [← hm, Finset.sum_mul]
    exact Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left (hb h) (mul_nonneg (hρ h) (hq h)))
  have hsecond : F ≤ (1-w)*(d+(1-pHat*s)*N) := by
    have hterm : ∀ h, ρ h*q h*bH h ≤ ρ h*q h*(d+(1-pHat*q h)*N) := by
      intro h
      by_cases hpos : 0 < q h
      · exact mul_le_mul_of_nonneg_left (htaper h hpos) (mul_nonneg (hρ h) (hq h))
      · have hz : q h=0 := le_antisymm (le_of_not_gt hpos) (hq h)
        simp only [hz, mul_zero, zero_mul, le_refl]
    have hsum := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) => hterm h)
    have hid : (∑ h, ρ h*q h*(d+(1-pHat*q h)*N)) = (1-w)*(d+(1-pHat*s)*N) := by
      simp_rw [show ∀ h, ρ h*q h*(d+(1-pHat*q h)*N) =
          (ρ h*q h)*(d+N)-(ρ h*(q h)^2)*(pHat*N) by intro h; ring]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hm, hs]
      ring
    exact hsum.trans_eq hid
  by_cases hzero : 1-w=0
  · have hw1 : w=1 := by linarith only [hzero]
    have hy1 : y=1 := le_antisymm hy (hw1 ▸ hw)
    simpa only [hw1, hy1, sub_self, zero_mul, add_zero] using hfirst
  · have hpos : 0 < 1-w := lt_of_le_of_ne (sub_nonneg.mpr (hw.trans hy)) (Ne.symm hzero)
    have h1 := mul_le_mul_of_nonneg_left hfirst (sub_nonneg.mpr hy)
    have h2 := mul_le_mul_of_nonneg_left hsecond (sub_nonneg.mpr hw)
    apply (mul_le_mul_iff_right₀ hpos).mp
    dsimp only [F] at h1 h2 ⊢
    nlinarith only [h1, h2]

theorem normalization_identity {I : Type*} [Fintype I]
    (π D N s : I → ℝ) (q K : I → I → ℝ) (x pHat : ℝ) {y L : ℝ}
    (hy : y ≠ 0) (hL : 0 ≤ L) (hD : average π D=1) :
    unnormalizedDrift (fun i => y*π i) (fun i => L*D i) (fun i => L*N i) s q K x y pHat =
      (y^2*L)*normalizedDrift π D N s q K x y pHat := by
  have hV : (∑ i, (y*π i)*(L*D i))=y*L := by
    simp only [mul_mul_mul_comm y _ L _, ← Finset.mul_sum]
    change y*L*average π D=y*L
    rw [hD, mul_one]
  have hw : ∀ i, (∑ t, (y*π t)*q i t)=y*average π (q i) := by
    intro i
    simp only [average, Finset.mul_sum, mul_assoc]
  have hk : ∀ i, (∑ t, (y*π t)*K i t*(L*D t)) =
      y*L*average π (fun t => K i t*D t) := by
    intro i
    simp only [average, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hh : ∀ i, (∑ t, (y*π t)*(1-q i t)*max (L*D t-(1+m x+B x*y)*(L*D i)) 0) =
      y*L*average π (fun t => (1-q i t)*max (D t-(1+m x+B x*y)*D i) 0) := by
    intro i
    simp only [average, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [show L*D t-(1+m x+B x*y)*(L*D i)=L*(D t-(1+m x+B x*y)*D i) by ring,
      ← mul_zero L, ← mul_max_of_nonneg _ _ hL]
    ring_nf
  unfold unnormalizedDrift normalizedDrift
  dsimp only
  rw [hV]
  simp_rw [hw, hk, hh]
  simp only [average]
  have hB : B x=2*P x := rfl
  rw [hB]
  have hconst : -(3*y+2*P x*(y-x)^2)*(y*L) =
      y^2*L*(-3-2*(P x*(y-x)^2/y)) := by field_simp [hy]; ring
  have hterms : (∑ i, y*π i*((y-y*∑ t, π t*q i t)*(L*D i+(1-pHat*s i)*(L*N i))+
      (1+m x+2*P x*y)*(y*∑ t, π t*q i t)*(L*D i)+
      2*P x*(y*L)*(y*∑ t, π t*q i t)+2*P x*(y*L*∑ t, π t*(K i t*D t))-
      y*L*∑ t, π t*((1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0))) =
      ∑ i, y^2*L*(π i*((1-∑ t, π t*q i t)*(D i+(1-pHat*s i)*N i)+
        (1+m x+2*P x*y)*(∑ t, π t*q i t)*D i+2*P x*y*(∑ t, π t*q i t)+
        2*P x*(∑ t, π t*(K i t*D t))-
        ∑ t, π t*((1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0))) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [mul_add, Finset.mul_sum]
  exact congrArg₂ (·+·) hconst hterms

theorem unnormalized_drift_le {I : Type*} [Fintype I]
    {μ d N s : I → ℝ} {q K : I → I → ℝ} {x y pHat ζ : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 < y) (hy : y ≤ 1)
    (hμ0 : ∀ i, 0 ≤ μ i) (hμ : ∑ i, μ i=y)
    (hd0 : ∀ i, 0 ≤ d i) (hV : 0 < ∑ i, μ i*d i) (hN : ∀ i, 0 ≤ N i)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
    (he : |pHat-P x| ≤ ζ)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ d i+d t)
    (hK : ∀ i t, K i t ≤
      (s i*(1-∑ u, μ u*q i u)+s t*(1-∑ u, μ u*q t u))/2) :
    unnormalizedDrift μ d N s q K x y pHat ≤ 12*ζ*(∑ i, μ i*d i) := by
  let V := ∑ i, μ i*d i
  let L := V/y
  let π := fun i => μ i/y
  let D := fun i => d i/L
  let R := fun i => N i/L
  have hyne := ne_of_gt hy0
  have hLpos : 0 < L := div_pos hV hy0
  have hLne := ne_of_gt hLpos
  have hyL : y*L=V := by dsimp only [L]; exact mul_div_cancel₀ _ hyne
  have hπ0 : ∀ i, 0 ≤ π i := fun i => div_nonneg (hμ0 i) hy0.le
  have hπ : ∑ i, π i=1 := by dsimp only [π]; rw [← Finset.sum_div, hμ, div_self hyne]
  have hμid : ∀ i, y*π i=μ i := fun i => mul_div_cancel₀ _ hyne
  have hdid : ∀ i, L*D i=d i := fun i => mul_div_cancel₀ _ hLne
  have hNid : ∀ i, L*R i=N i := fun i => mul_div_cancel₀ _ hLne
  have hD : average π D=1 := by
    unfold average
    simp_rw [show ∀ i, π i*D i=(μ i*d i)/(y*L) by intro i; dsimp only [π, D]; ring]
    rw [← Finset.sum_div, hyL, div_self (ne_of_gt hV)]
  have hD0 : ∀ i, 0 ≤ D i := fun i => div_nonneg (hd0 i) hLpos.le
  have hR0 : ∀ i, 0 ≤ R i := fun i => div_nonneg (hN i) hLpos.le
  have hcomp' : ∀ i t, q i t < 1 → R i*(1-pHat*q i t) ≤ D i+D t := by
    intro i t hit
    have hh := div_le_div_of_nonneg_right (hcomp i t hit) hLpos.le
    dsimp only [R, D]
    simpa only [div_mul_eq_mul_div, add_div] using hh
  have hw : ∀ i, y*average π (q i)=∑ u, μ u*q i u := by
    intro i
    simp only [average, Finset.mul_sum, ← mul_assoc, hμid]
  have hK' : ∀ i t, K i t ≤
      (s i*(1-y*average π (q i))+s t*(1-y*average π (q t)))/2 := by
    intro i t
    simpa only [hw] using hK i t
  have hh := normalized_drift_le hx0 hx hy0 hy hπ0 hπ hD0 hD hR0 hs0 hs
    hq0 hq hp0 hp hζ0 hζ he hcomp' hK'
  have hnorm := normalization_identity π D R s q K x pHat hyne hLpos.le hD
  simp only [hμid, hdid, hNid] at hnorm
  rw [hnorm]
  have hscale := mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg y) hLpos.le)
  have hV0 : 0 ≤ V := hV.le
  have hyV := mul_le_of_le_one_left hV0 hy
  have hprod := mul_le_mul_of_nonneg_left hyV (mul_nonneg (by norm_num : (0:ℝ) ≤ 12) hζ0)
  have heq : y^2*L=y*V := by calc
    y^2*L = y*(y*L) := by ring
    _ = y*V := by rw [hyL]
  rw [heq] at hscale ⊢
  calc
    y*V*normalizedDrift π D R s q K x y pHat ≤ y*V*(12*ζ) := hscale
    _ = 12*ζ*(y*V) := by ring
    _ ≤ 12*ζ*V := hprod

end MetricKMedian.GraphComparison
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_UniformDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GraphComparison
open Analytic

variable {I : Type*} [Fintype I]

theorem uniform_zero_drift {g y pHat : ℝ} {d N s : I → ℝ} {q K : I → I → ℝ}
    (hg : 0 < g) (hy : ∑ _i : I, g=y)
    (hd : ∀ i, 0 ≤ d i) (hV : ∑ i, g*d i=0)
    (hN : ∀ i, 0 ≤ N i) (hp : pHat ≤ 1/2)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ d i+d t) (x : ℝ) :
    unnormalizedDrift (fun _ => g) d N s q K x y pHat=0 := by
  have hd0 : ∀ i, d i=0 := by
    intro i
    have hterm := Finset.single_le_sum (s := Finset.univ)
      (fun t _ => mul_nonneg hg.le (hd t)) (Finset.mem_univ i)
    rw [hV] at hterm
    exact le_antisymm (by nlinarith only [hterm, hg]) (hd i)
  have hrad : ∀ i, (y-∑ t, g*q i t)*N i=0 := by
    intro i
    by_cases hNi : N i=0
    · rw [hNi, mul_zero]
    have hNp : 0 < N i := lt_of_le_of_ne (hN i) (Ne.symm hNi)
    have hrow : ∀ t, q i t=1 := by
      intro t
      apply le_antisymm (hq i t)
      by_contra hn
      have ht := hcomp i t (lt_of_not_ge hn)
      rw [hd0 i, hd0 t, add_zero] at ht
      have hprod := mul_le_mul hp (hq i t) (hq0 i t) (by norm_num : (0:ℝ) ≤ 1/2)
      have hden : 0 < 1-pHat*q i t := by nlinarith only [hprod]
      exact (not_lt_of_ge ht) (mul_pos hNp hden)
    simp only [hrow, mul_one, hy, sub_self, zero_mul]
  unfold unnormalizedDrift
  simp only [hd0, mul_zero, sub_zero, max_self, Finset.sum_const_zero,
    zero_mul, add_zero, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  have hi := hrad i
  calc
    g*((y-∑ t, g*q i t)*((1-pHat*s i)*N i)) = g*(1-pHat*s i)*((y-∑ t, g*q i t)*N i) := by ring
    _ = 0 := by rw [hi, mul_zero]

theorem uniform_drift_le {g x y pHat ζ : ℝ} {d N s : I → ℝ} {q K : I → I → ℝ}
    (hg : 0 < g) (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hysum : ∑ _i : I, g=y) (hy : y ≤ 1)
    (hd : ∀ i, 0 ≤ d i) (hN : ∀ i, 0 ≤ N i)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
    (he : |pHat-Analytic.P x| ≤ ζ)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ d i+d t)
    (hK : ∀ i t, K i t ≤
      (s i*(1-∑ u, g*q i u)+s t*(1-∑ u, g*q t u))/2) :
    unnormalizedDrift (fun _ => g) d N s q K x y pHat ≤ 12*ζ*(∑ i, g*d i) := by
  have hV0 : 0 ≤ ∑ i, g*d i := Finset.sum_nonneg (fun i _ => mul_nonneg hg.le (hd i))
  rcases eq_or_lt_of_le hV0 with hz | hV
  · rw [uniform_zero_drift hg hysum hd hz.symm hN hp hq0 hq hcomp x, ← hz, mul_zero]
  have hy0 : 0 < y := by
    by_contra hn
    have hzero : ∀ i : I, g=0 := by
      intro i
      have ht := Finset.single_le_sum (s := Finset.univ) (f := fun _ : I => g)
        (fun _ _ => hg.le) (Finset.mem_univ i)
      rw [hysum] at ht
      exact le_antisymm (ht.trans (le_of_not_gt hn)) hg.le
    have hz : ∑ i, g*d i=0 := Finset.sum_eq_zero (fun i _ => by rw [hzero i, zero_mul])
    exact (ne_of_gt hV) hz
  exact unnormalized_drift_le hx0 hx hy0 hy (fun _ => hg.le) hysum hd hV hN
    hs0 hs hq0 hq hp0 hp hζ0 hζ he hcomp hK

end MetricKMedian.GraphComparison
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_AveragedGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GeneratorAverage
open Analytic GraphComparison GraphMoments

variable {Ω I H : Type*} [Fintype Ω] [Fintype I] [Fintype H] [DecidableEq I]

theorem averaged_ideal_drift_s53_oai (μ : FiniteLaw Ω) {g x y pHat ζ b : ℝ}
    (d N : I → ℝ) (bH : H → ℝ)
    (XI : Ω → I → I → ℝ) (XE : Ω → H → I → ℝ)
    (qI : I → I → ℝ) (qE : H → I → ℝ)
    (hg : 0 < g) (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hysum : ∑ _i : I, g=y) (hy : y ≤ 1)
    (hd : ∀ i, 0 ≤ d i) (hN : ∀ i, 0 ≤ N i)
    (hqI0 : ∀ h i, 0 ≤ qI h i) (hqI : ∀ h i, qI h i ≤ 1)
    (hqE0 : ∀ h i, 0 ≤ qE h i) (hqE : ∀ h i, qE h i ≤ 1)
    (hmass : ∀ i, (∑ h, g*qE h i)=1-∑ t, g*qI t i)
    (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
    (he : |pHat-Analytic.P x| ≤ ζ)
    (hcomp : ∀ i t, qI t i < 1 → N i*(1-pHat*qI t i) ≤ d i+d t)
    (hb : ∀ h, bH h ≤ b)
    (htaper : ∀ h i, 0 < qE h i → bH h ≤ d i+(1-pHat*qE h i)*N i)
    (hfirstI : ∀ h i, μ.expect (fun ω => XI ω h i)=qI h i)
    (hfirstE : ∀ h i, μ.expect (fun ω => XE ω h i)=qE h i)
    (hidem : ∀ ω h i, XE ω h i*XE ω h i=XE ω h i)
    (hpair : ∀ h i t, i ≠ t → μ.expect (fun ω => XE ω h i*XE ω h t)=qE h i*qE h t) :
    let V := ∑ i, g*d i
    let a := coefficient x y
    2*x*(y-x)*moment 2 x*V+
      μ.expect (fun ω => inside g a (a*V+(1-y)*b) d XI ω+
        external g a (Analytic.B x) V bH d XE ω) ≤
      Analytic.B x*g*V+12*ζ*V := by
  let s := rowType (fun _ : H => g) (fun i h => qE h i)
  have hrow := row_type_bounds (fun _ : H => hg.le)
    (fun i h => hqE0 h i) (fun i h => hqE h i)
  have hs0 : ∀ i, 0 ≤ s i := fun i => (hrow i).1
  have hs : ∀ i, s i ≤ 1 := fun i => (hrow i).2.1
  have hsEq : ∀ i, (∑ h, g*(qE h i)^2)=s i*(1-∑ t, g*qI t i) := by
    intro i
    have hh := (hrow i).2.2
    change s i*(∑ h, g*qE h i)=(∑ h, g*(qE h i)^2) at hh
    rw [hmass i] at hh
    exact hh.symm
  have hw0 : ∀ i, 0 ≤ ∑ t, g*qI t i := fun i =>
    Finset.sum_nonneg (fun t _ => mul_nonneg hg.le (hqI0 t i))
  have hw : ∀ i, (∑ t, g*qI t i) ≤ y := by
    intro i
    rw [← hysum]
    exact Finset.sum_le_sum (fun t _ => mul_le_of_le_one_right hg.le (hqI t i))
  have hincoming : ∀ i, (∑ h, g*qE h i) ≤ 1 := by
    intro i
    rw [hmass]
    linarith only [hw0 i]
  have hcap : ∀ i, (∑ h, g*qE h i*bH h) ≤
      (1-y)*b+(y-∑ t, g*qI t i)*(d i+(1-pHat*s i)*N i) := by
    intro i
    exact cap_average (fun _ => hg.le) (fun h => hqE0 h i) (hw i) hy
      (hmass i) (hsEq i) hb (fun h => htaper h i)
  have hK : ∀ i t, GraphMoments.kernel g qE i t ≤
      (s i*(1-∑ u, g*qI u i)+s t*(1-∑ u, g*qI u t))/2 := by
    intro i t
    have hh := GraphComparison.kernel_bound (q := fun i h => qE h i)
      (fun _ : H => hg.le) i t
    change GraphMoments.kernel g qE i t ≤
      ((∑ h, g*(qE h i)^2)+(∑ h, g*(qE h t)^2))/2 at hh
    simpa only [hsEq] using hh
  have hgeneration := expanded_bound_s53 (x := x) μ d N s bH XI XE qI qE hg.le hd hysum
    hmass hincoming hfirstI hfirstE hidem hpair hcap
  have hdrift := uniform_drift_le hg hx0 hx hysum hy hd hN hs0 hs
    (fun i t => hqI0 t i) (fun i t => hqI t i) hp0 hp hζ0 hζ he hcomp hK
  dsimp only at hgeneration ⊢
  linarith only [hgeneration, hdrift]

end MetricKMedian.GeneratorAverage
end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift_s53_oai.{u_1, u_2, u_3} := @OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift_s53_oai.{u_1, u_2, u_3}
