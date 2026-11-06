-- Prove2me | solution 1 for ManyServerFluid.Uniqueness.eq_4_55
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T19:40:45.922455+00:00
-- url     : https://prove2.me/submissions/fb9a5888-bc19-49b8-a35d-9354200db9b3

import Mathlib
import Definitions.Def_ManyServerFluid_Uniqueness_Model
import Definitions.Def_ManyServerFluid_Uniqueness_AgeEquation
open MeasureTheory Filter Topology Set
open scoped ENNReal

open ManyServerFluid.Uniqueness

namespace MSFEq455

/-- Lipschitz ∘ absolutely continuous is absolutely continuous. -/
lemma ac_comp_lipschitz {f φ : ℝ → ℝ} {a b : ℝ} {T : Set ℝ} {K : NNReal}
    (hf : AbsolutelyContinuousOnInterval f a b) (hφ : LipschitzOnWith K φ T)
    (hmap : ∀ y ∈ uIcc a b, f y ∈ T) :
    AbsolutelyContinuousOnInterval (fun y => φ (f y)) a b := by
  unfold AbsolutelyContinuousOnInterval at *
  have hK : Tendsto (fun E : ℕ × (ℕ → ℝ × ℝ) =>
      (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) := by
    simpa using hf.const_mul (K : ℝ)
  refine squeeze_zero' (Eventually.of_forall fun E => Finset.sum_nonneg
    (fun _ _ => dist_nonneg)) ?_ hK
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with E hE
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact hφ.dist_le_mul _ (hmap _ (hE.1 i hi).1) _ (hmap _ (hE.1 i hi).2)

variable (S : ServiceLaw)

lemma G_eq_intervalIntegral (x : ℝ) : S.G x = ∫ y in (0 : ℝ)..x, S.g y := by
  have hint : ∀ c : ℝ, IntegrableOn S.g (Iic c) := fun c => S.integrable_g.integrableOn
  have h0 : S.G 0 = 0 := by
    unfold ServiceLaw.G
    apply setIntegral_eq_zero_of_ae_eq_zero
    have : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [this] with y hy hyI
    exact S.g_eq_zero_of_neg y (lt_of_le_of_ne hyI hy)
  have := intervalIntegral.integral_Iic_sub_Iic (hint 0) (hint x)
  unfold ServiceLaw.G at h0 ⊢
  rw [← this, h0, sub_zero]

lemma G_mono : Monotone S.G := by
  intro a b hab
  rw [G_eq_intervalIntegral, G_eq_intervalIntegral]
  have h := intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := a) (c := b)
      (S.integrable_g.intervalIntegrable (μ := volume))
      (S.integrable_g.intervalIntegrable (μ := volume))
  have : 0 ≤ ∫ y in a..b, S.g y :=
    intervalIntegral.integral_nonneg hab (fun y _ => S.g_nonneg y)
  linarith

lemma G_lt_one {x : ℝ} (hx : x ∈ S.Ages) : S.G x < 1 := by
  obtain ⟨_, hxM⟩ := hx
  unfold ServiceLaw.M at hxM
  rw [lt_iSup_iff] at hxM
  obtain ⟨x', hx'⟩ := hxM
  rw [lt_iSup_iff] at hx'
  obtain ⟨⟨h0, hG⟩, hlt⟩ := hx'
  have : x < x' := by
    rcases le_or_gt x' x with h | h
    · exact absurd hlt (not_lt.mpr (ENNReal.ofReal_le_ofReal h))
    · exact h
  exact lt_of_le_of_lt (G_mono S this.le) hG

lemma G_zero : S.G 0 = 0 := by
  rw [G_eq_intervalIntegral]; simp

/-- ∫_a^x h = log(1 − G a) − log(1 − G x) for 0 ≤ a ≤ x ∈ [0, M). -/
lemma integral_h {a x : ℝ} (hax : a ≤ x) (hx : x ∈ S.Ages) :
    ∫ y in a..x, S.h y = Real.log (1 - S.G a) - Real.log (1 - S.G x) := by
  set c := 1 - S.G x with hc
  have hcpos : 0 < c := by have := G_lt_one S hx; linarith
  have hge : ∀ y ≤ x, c ≤ 1 - S.G y := fun y hy => by
    have := G_mono S hy; linarith
  -- 1 - G is AC on [a, x]
  have hGac : AbsolutelyContinuousOnInterval (fun y => 1 - S.G y) a x := by
    have h1 := (S.integrable_g.intervalIntegrable (a := a) (b := x)
      ).absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
    have h2 : AbsolutelyContinuousOnInterval (fun y => (1 - ∫ v in (0:ℝ)..a, S.g v) -
        ∫ v in a..y, S.g v) a x := by
      have hc1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ) -
          ∫ v in (0:ℝ)..a, S.g v) a x := by
        apply LipschitzOnWith.absolutelyContinuousOnInterval (K := 0)
        exact LipschitzWith.lipschitzOnWith (LipschitzWith.const _)
      exact hc1.fun_sub h1
    convert h2 using 2 with y
    rw [G_eq_intervalIntegral, ← intervalIntegral.integral_add_adjacent_intervals (b := a)
      (S.integrable_g.intervalIntegrable) (S.integrable_g.intervalIntegrable)]
    ring
  have hlip : LipschitzOnWith (Real.toNNReal c⁻¹) Real.log (Ici c) := by
    apply (convex_Ici c).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (f' := fun y => y⁻¹)
    · intro y hy
      exact (Real.hasDerivAt_log (lt_of_lt_of_le hcpos hy).ne').hasDerivWithinAt
    · intro y hy
      have hy' : c ≤ y := hy
      have hypos : 0 < y := lt_of_lt_of_le hcpos hy'
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_inv, abs_of_pos hypos,
        Real.coe_toNNReal _ (inv_nonneg.mpr hcpos.le)]
      exact inv_anti₀ hcpos hy'
  have hLac : AbsolutelyContinuousOnInterval (fun y => Real.log (1 - S.G y)) a x := by
    refine ac_comp_lipschitz hGac hlip ?_
    intro y hy
    rw [uIcc_of_le hax] at hy
    exact hge y hy.2
  have hFTC := hLac.integral_deriv_eq_sub
  rw [← neg_sub, ← hFTC, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr_ae
  have hloc : LocallyIntegrable S.g volume := S.integrable_g.locallyIntegrable
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hloc] with y hy hyI
  rw [uIoc_of_le hax] at hyI
  have hGd : HasDerivAt S.G (S.g y) y := by
    have := hy 0
    have heq : (fun x => ∫ t in (0:ℝ)..x, S.g t) = S.G := by
      funext z; rw [G_eq_intervalIntegral]
    rwa [heq] at this
  have hne : 1 - S.G y ≠ 0 := (lt_of_lt_of_le hcpos (hge y hyI.2)).ne'
  have hd : HasDerivAt (fun y => Real.log (1 - S.G y)) (-(S.g y) / (1 - S.G y)) y := by
    have := ((hasDerivAt_const y (1:ℝ)).sub hGd).log hne
    simpa using this
  rw [hd.deriv]
  unfold ServiceLaw.h
  ring

lemma psi_formula {a x : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) (hx : x ∈ S.Ages) :
    Real.exp (-∫ y in a..x, S.h y) = (1 - S.G x) / (1 - S.G a) := by
  have h1 : 0 < 1 - S.G x := by have := G_lt_one S hx; linarith
  have h2 : 0 < 1 - S.G a := by
    have := G_lt_one S ⟨ha, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hax) hx.2⟩; linarith
  rw [integral_h S hax hx, neg_sub, Real.exp_sub, Real.exp_log h1, Real.exp_log h2]

end MSFEq455

open MSFEq455 in
theorem solution (S : ServiceLaw) (x t : ℝ) (hx : x ∈ S.Ages) :
    (0 ≤ t → t ≤ x → S.psiEll S.h (x, t) = (1 - S.G x) / (1 - S.G (x - t))) ∧
    (x ≤ t → S.psiEll S.h (x, t) = 1 - S.G x) := by
  constructor
  · intro ht htx
    unfold ServiceLaw.psiEll ServiceLaw.rEll
    rw [if_pos ⟨ht, htx, hx.2⟩]
    exact psi_formula S (by linarith) (by linarith) hx
  · intro hxt
    unfold ServiceLaw.psiEll ServiceLaw.rEll
    by_cases h1 : 0 ≤ t ∧ t ≤ x ∧ ENNReal.ofReal x < S.M
    · rw [if_pos h1]
      have : t = x := le_antisymm h1.2.1 hxt
      subst this
      rw [sub_self, psi_formula S le_rfl hx.1 hx, G_zero, sub_zero, div_one]
    · rw [if_neg h1, if_pos ⟨hx.1, hxt, hx.2⟩]
      rw [psi_formula S le_rfl hx.1 hx, G_zero, sub_zero, div_one]
