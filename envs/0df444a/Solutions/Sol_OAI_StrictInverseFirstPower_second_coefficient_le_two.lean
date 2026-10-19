-- Prove2me | solution 1 for OAI.StrictInverseFirstPower.second_coefficient_le_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:28:06.735651+00:00
-- url     : https://prove2.me/submissions/f9e92b70-4cd2-4964-9448-39852634cb13

import Mathlib
import Theorems.Thm_OAI_StrictInverseFirstPower_pole_coefficient_le_one

section
-- module Solutions.OAIQW_StrictInverseFirstPower.RootTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate

open Set Filter Metric Complex
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

theorem hasDerivAt_continuous_squareRoot {f g : ℂ → ℂ} {z d : ℂ}
    (hf : HasDerivAt f d z) (hg : ContinuousAt g z) (hg0 : g z ≠ 0)
    (hsq : ∀ᶠ w in 𝓝 z, g w ^ 2 = f w) :
    HasDerivAt g (d / (2 * g z)) z := by
  have hden : g z + g z ≠ 0 := by simpa only [← two_mul] using mul_ne_zero two_ne_zero hg0
  have hd : ∀ᶠ w in 𝓝 z, g w + g z ≠ 0 := (hg.add_const _).eventually_ne hden
  rw [hasDerivAt_iff_tendsto_slope]
  have ht := (hasDerivAt_iff_tendsto_slope.mp hf).div
    ((hg.add_const _).tendsto.mono_left nhdsWithin_le_nhds) hden
  have he : (fun w => slope f z w / (g w + g z)) =ᶠ[𝓝[≠] z] slope g z := by
    filter_upwards [hsq.filter_mono nhdsWithin_le_nhds, hd.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with w hw hwd hwz
    rw [slope_def_field, slope_def_field, ← hw, ← hsq.self_of_nhds]
    field_simp
    ring
  simpa only [← two_mul] using ht.congr' he

theorem exists_holomorphic_squareRoot {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hc : IsSimplyConnected U) (hf : DifferentiableOn ℂ f U)
    (hzero : ∀ z ∈ U, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, g z ^ 2 = f z := by
  have hz : 0 ∉ f '' U := by
    rintro ⟨z, hz, he⟩
    exact hzero z hz he
  obtain ⟨g, hg, hsq⟩ := Complex.exists_continuousOn_pow_eq hc hU hf.continuousOn hz (by decide : 2 ≠ 0)
  refine ⟨g, fun z hz => ?_, fun z _ => hsq z⟩
  have hgn : g z ≠ 0 := by
    intro he
    apply hzero z hz
    rw [← hsq z, he, zero_pow (by decide : 2 ≠ 0)]
  exact (hasDerivAt_continuous_squareRoot (hf.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    (hg.continuousAt (hU.mem_nhds hz)) hgn (Filter.Eventually.of_forall hsq)).differentiableAt.differentiableWithinAt

theorem exists_normalized_holomorphic_squareRoot {U : Set ℂ} {f : ℂ → ℂ} {a : ℂ}
    (hU : IsOpen U) (hc : IsSimplyConnected U) (hf : DifferentiableOn ℂ f U)
    (hzero : ∀ z ∈ U, f z ≠ 0) (ha : a ∈ U) (hfa : f a = 1) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ (∀ z ∈ U, g z ^ 2 = f z) ∧ g a = 1 := by
  obtain ⟨g, hg, hsq⟩ := exists_holomorphic_squareRoot hU hc hf hzero
  have hga : g a ^ 2 = 1 := (hsq a ha).trans hfa
  have hgn : g a ≠ 0 := by intro he; simp [he] at hga
  refine ⟨fun w => g w / g a, hg.div_const _, ?_, div_self hgn⟩
  intro w hw
  rw [div_pow, hsq w hw, hga, div_one]

end
end StrictInverseFirstPower

namespace StrictInverseFirstPower
noncomputable section

lemma simplyConnected_disk : IsSimplyConnected (ball (0 : ℂ) 1) := by
  let := (convex_ball (0 : ℂ) (1 : ℝ)).contractibleSpace ⟨0, by simp⟩
  change SimplyConnectedSpace (ball (0 : ℂ) 1)
  exact inferInstance

lemma sq_mem_disk {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : z ^ 2 ∈ ball (0 : ℂ) 1 := by
  simp only [mem_ball, dist_zero_right, norm_pow] at *
  nlinarith [norm_nonneg z]

lemma mul_dslope_zero (f : ℂ → ℂ) (hf0 : f 0 = 0) (z : ℂ) :
    z * dslope f 0 z = f z := by
  simpa [hf0, smul_eq_mul] using sub_smul_dslope f (0 : ℂ) z

theorem exists_odd_root_transform {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 1) ∧ g 0 = 1 ∧
      (∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, g z ^ 2 = dslope f 0 z) ∧
      InjOn (fun z => z * g (z ^ 2)) (ball 0 1) := by
  have hdU : DifferentiableOn ℂ (dslope f 0) (ball 0 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (by simp))).mpr hd
  have hu0 : dslope f 0 0 = 1 := by simpa using h1
  have hun (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : dslope f 0 z ≠ 0 := by
    intro he
    by_cases hz0 : z = 0
    · simp [hz0, h1] at he
    · apply hz0
      apply hi hz (by simp)
      rw [← mul_dslope_zero f h0 z, he, mul_zero, h0]
  obtain ⟨g, hg, hgsq, hg0⟩ := exists_normalized_holomorphic_squareRoot
    isOpen_ball simplyConnected_disk hdU hun (by simp) hu0
  have hgn (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : g z ≠ 0 := by
    intro he
    apply hun z hz
    rw [← hgsq z hz, he, zero_pow (by decide : 2 ≠ 0)]
  refine ⟨g, hg, hg0, hgn, hgsq, ?_⟩
  intro z hz w hw he
  have he2 : z ^ 2 = w ^ 2 := by
    apply hi (sq_mem_disk hz) (sq_mem_disk hw)
    calc f (z ^ 2) = (z * g (z ^ 2)) ^ 2 := by
          rw [mul_pow, hgsq _ (sq_mem_disk hz), mul_dslope_zero f h0]
         _ = (w * g (w ^ 2)) ^ 2 := congrArg (· ^ 2) he
         _ = f (w ^ 2) := by
          rw [mul_pow, hgsq _ (sq_mem_disk hw), mul_dslope_zero f h0]
  dsimp only at he
  rw [he2] at he
  exact mul_right_cancel₀ (hgn _ (sq_mem_disk hw)) he

theorem second_coefficient_le_two_oai {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) : ‖deriv (dslope f 0) 0‖ ≤ 2 := by
  obtain ⟨g, hg, hg0, hgn, hgsq, hqi⟩ := exists_odd_root_transform hd hi h0 h1
  let v : ℂ → ℂ := fun z => (g z)⁻¹
  have hv : DifferentiableOn ℂ v (ball 0 1) := hg.inv hgn
  have hv0 : v 0 = 1 := by simp [v, hg0]
  let H : ℂ → ℂ := fun z => z * dslope v 0 (z ^ 2)
  have hds : DifferentiableOn ℂ (dslope v 0) (ball 0 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (by simp))).mpr hv
  have hH : DifferentiableOn ℂ H (ball 0 1) := differentiableOn_id.mul
    (hds.comp (differentiableOn_id.pow 2) (fun _ hz => sq_mem_disk hz))
  have hH0 : H 0 = 0 := by simp [H]
  have hG (z : ℂ) (hz : z ≠ 0) : z⁻¹ + H z = (z * g (z ^ 2))⁻¹ := by
    have hs := sub_smul_dslope v (0 : ℂ) (z ^ 2)
    simp only [sub_zero, smul_eq_mul, hv0] at hs
    dsimp only [H]
    rw [mul_inv_rev]
    dsimp only [v] at hs
    field_simp
    linear_combination hs
  have hGi : InjOn (fun z => z⁻¹ + H z) (ball 0 1 \ {0}) := by
    intro z hz w hw he
    dsimp only at he
    rw [hG z hz.2, hG w hw.2, inv_inj] at he
    exact hqi hz.1 hw.1 he
  have ha := pole_coefficient_le_one hH hH0 hGi
  have hd0 := hg.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hvd : HasDerivAt v (-deriv g 0) 0 := by
    convert hd0.hasDerivAt.inv (hgn 0 (by simp)) using 1
    all_goals first | rfl | simp [hg0]
  have hHd : deriv H 0 = -deriv g 0 := by
    have hp : HasDerivAt (fun z : ℂ => z ^ 2) 0 0 := by
      convert (hasDerivAt_id (0 : ℂ)).pow 2 using 1 <;> first | rfl | norm_num
    have hdss : HasDerivAt (dslope v 0) (deriv (dslope v 0) (0 ^ 2)) (0 ^ 2) :=
      (hds.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ^ 2 ∈ ball 0 1))).hasDerivAt
    have he := (hasDerivAt_id (0 : ℂ)).mul (hdss.comp (0 : ℂ) hp)
    convert he.deriv using 1 <;> first | rfl | simp [hvd.deriv]
  have hud : deriv (dslope f 0) 0 = 2 * deriv g 0 := by
    have he : (fun z => g z ^ 2) =ᶠ[𝓝 (0 : ℂ)] dslope f 0 := by
      filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1)] with z hz
      exact hgsq z hz
    have hp : HasDerivAt (fun z => g z ^ 2) (2 * deriv g 0) 0 := by
      convert hd0.hasDerivAt.pow 2 using 1
      all_goals first | rfl | simp [hg0]
    exact (hp.congr_of_eventuallyEq he.symm).deriv
  rw [hHd, norm_neg] at ha
  rw [hud, norm_mul]
  norm_num
  linarith

end
end StrictInverseFirstPower

end

end OAI
end

theorem solution : type_of% @OAI.StrictInverseFirstPower.second_coefficient_le_two_oai := @OAI.StrictInverseFirstPower.second_coefficient_le_two_oai
