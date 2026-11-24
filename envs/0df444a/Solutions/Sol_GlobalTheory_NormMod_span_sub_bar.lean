-- Prove2me | solution 1 for GlobalTheory.NormMod.span_sub_bar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:14:43.185177+00:00
-- url     : https://prove2.me/submissions/1099e786-d16f-4e29-9865-11e08d6544ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormMod
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HostModel
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
namespace GlobalTheory.NormMod
theorem _root_.solution : Ideal.span (Set.range fun b : 𝓞 E => b - H.bar b) = ⊤ := by
  haveI := H.unram
  let σ := IsCMField.ringOfIntegersComplexConj E
  have hσ : ∀ a, σ a = H.bar a := fun a => by
    apply RingOfIntegers.ext
    exact (IsCMField.coe_ringOfIntegersComplexConj E a).trans (H.bar_eq a).symm
  let L : 𝓞 E ⊗[𝓞 (maximalRealSubfield E)] 𝓞 E →ₐ[𝓞 (maximalRealSubfield E)] 𝓞 E :=
    Algebra.TensorProduct.lift (AlgHom.id _ _) (σ : 𝓞 E →ₐ[_] 𝓞 E) fun _ _ => Commute.all _ _
  have hL : ∀ x y, L (x ⊗ₜ y) = x * H.bar y := fun x y => by simp [L, hσ]
  have h1 : ∀ z, Algebra.TensorProduct.lmul' (𝓞 (maximalRealSubfield E)) (S := 𝓞 E) z - L z ∈
      Ideal.span (Set.range fun b : 𝓞 E => b - H.bar b) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [hL, Algebra.TensorProduct.lmul'_apply_tmul, ← mul_sub]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨y, rfl⟩)
    | add x y hx hy =>
      rw [map_add, map_add]
      convert Ideal.add_mem _ hx hy using 1
      ring
  have h2 := congrArg L
    (Algebra.FormallyUnramified.one_tmul_mul_elem (R := 𝓞 (maximalRealSubfield E)) H.rt)
  rw [map_mul, map_mul, hL, hL, bar_rt, map_one] at h2
  have h3 : L (Algebra.FormallyUnramified.elem (𝓞 (maximalRealSubfield E)) (𝓞 E)) = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero : (2 : 𝓞 E) ≠ 0) (rt_ne_zero H))
    linear_combination -h2
  have h4 := h1 (Algebra.FormallyUnramified.elem (𝓞 (maximalRealSubfield E)) (𝓞 E))
  rw [h3, Algebra.FormallyUnramified.lmul_elem, sub_zero] at h4
  exact (Ideal.eq_top_iff_one _).2 h4
end GlobalTheory.NormMod
