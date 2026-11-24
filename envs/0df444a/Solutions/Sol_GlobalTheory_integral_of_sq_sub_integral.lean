-- Prove2me | solution 1 for GlobalTheory.integral_of_sq_sub_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:01:24.726502+00:00
-- url     : https://prove2.me/submissions/1da763b9-f828-4d7e-9730-8cfe805c4597

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationLeOneOfSqSubSelfIntegralBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    {ι : Type} [Fintype ι] (b : Module.Basis ι E E') (hbi : ∀ i, IsIntegral ℤ (b i))
    (w : HeightOneSpectrum (𝓞 E)) (w'' : HeightOneSpectrum (𝓞 E'))
    (hw : w''.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal) (ε : E')
    (hε : ∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) : w''.valuation E' ε ≤ 1 := by
  have hunder : w''.under (𝓞 E) = w := HeightOneSpectrum.ext hw
  have hc : ∀ c : E, w.valuation E c ≤ 1 → w''.valuation E' (algebraMap E E' c) ≤ 1 := by
    intro c hc
    subst hunder
    have : w''.asIdeal.LiesOver (w''.under (𝓞 E)).asIdeal := ⟨rfl⟩
    rw [← HeightOneSpectrum.valuation_liesOver E' (w''.under (𝓞 E)) w'' c]
    exact pow_le_one' hc _
  have hb : ∀ i, w''.valuation E' (b i) ≤ 1 := by
    intro i
    have : b i = algebraMap (𝓞 E') E' (⟨b i, (mem_integralClosure_iff ℤ E').2 (hbi i)⟩ : 𝓞 E') := rfl
    rw [this]
    exact w''.valuation_le_one _
  have hu : w''.valuation E' (ε * ε - ε) ≤ 1 := by
    rw [← b.sum_repr (ε * ε - ε)]
    refine (Valuation.map_sum_le _ fun i _ => ?_)
    rw [Algebra.smul_def, map_mul]
    exact mul_le_one' (hc _ (hε i)) (hb i)
  by_contra h
  push_neg at h
  have h2 : w''.valuation E' (ε * ε) ≤ w''.valuation E' ε := by
    have : ε * ε = ε + (ε * ε - ε) := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le le_rfl (hu.trans h.le))
  rw [map_mul] at h2
  have h0 : (0 : _) < w''.valuation E' ε := lt_trans zero_lt_one h
  have := mul_lt_mul_of_pos_left h h0
  rw [mul_one] at this
  exact absurd h2 (not_le.2 this)
end GlobalTheory
