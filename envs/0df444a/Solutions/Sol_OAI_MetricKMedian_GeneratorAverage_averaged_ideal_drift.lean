-- Prove2me | solution 1 for OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:38:17.491725+00:00
-- url     : https://prove2.me/submissions/37a167da-c804-4ad2-bec3-ff69256a5368
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ035K021
import Theorems.Thm_OAI_MetricKMedian_GeneratorAverage_expanded_bound
import Theorems.Thm_OAI_MetricKMedian_GraphComparison_unnormalized_drift_le

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphComparison
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

end MetricKMedian.GraphComparison
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_AveragedDrift
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

end MetricKMedian.GraphComparison
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_UniformDrift
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
-- module Solutions.OAIQ035_KM.KMedian_Process_AveragedGenerator
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

theorem averaged_ideal_drift_oai (μ : FiniteLaw Ω) {g x y pHat ζ b : ℝ}
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
  have hgeneration := expanded_bound (x := x) μ d N s bH XI XE qI qE hg.le hd hysum
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

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift_oai.{u_1, u_2, u_3} := @OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift_oai.{u_1, u_2, u_3}
