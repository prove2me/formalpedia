-- Prove2me | solution 1 for GlobalTheory.HermDen.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:14:52.745056+00:00
-- url     : https://prove2.me/submissions/b671c759-8e70-494c-8243-9ce4afd091a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegralConj
import Theorems.Thm_GlobalTheory_HermDen_isIntegral_conj
import Theorems.Thm_GlobalTheory_LatFin_exists_common_den


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.HermDen
open ReciprocityTheory.ChartRestriction.G.FD
namespace GlobalTheory.HermDen
theorem _root_.solution (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ den : 𝓞 E, den ≠ 0 ∧ ∀ x ∈ Λ, ∀ y ∈ Λ,
      IsIntegral ℤ ((den : E) * ReciprocityTheory.ChartRestriction.G.FD.herm G x y) := by
  classical
  obtain ⟨k, hk, hi⟩ := GlobalTheory.LatFin.exists_common_den Λ hΛ
  obtain ⟨l, hl, hG⟩ := GlobalTheory.LatFin.exists_common_den
    (Submodule.span (𝓞 E) (Set.range fun a : Fin r => (G a : Fin r → E)))
    (Submodule.fg_span (Set.finite_range _))
  have hG' : ∀ a b, IsIntegral ℤ ((l : E) * G a b) := fun a b =>
    hG _ (Submodule.subset_span ⟨a, rfl⟩) b
  refine ⟨((k * k * l : ℤ) : 𝓞 E), Int.cast_ne_zero.2 (mul_ne_zero (mul_ne_zero hk hk) hl),
    fun x hx y hy => ?_⟩
  have e : ((((k * k * l : ℤ) : 𝓞 E)) : E) * herm G x y
      = ∑ a, ∑ b, ((k : E) * x a) * ((l : E) * G a b) * cc ((k : E) * y b) := by
    have h1 : ((((k * k * l : ℤ) : 𝓞 E)) : E) = (k : E) * k * l := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_intCast]
      push_cast
      ring
    rw [h1, herm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h2 : cc ((k : E) * y b) = k * cc (y b) := by simp [cc]
    rw [h2]
    ring
  rw [e]
  exact IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ =>
    ((hi x hx a).mul (hG' a b)).mul (isIntegral_conj (hi y hy b))
end GlobalTheory.HermDen
