-- Prove2me | solution 1 for GlobalTheory.PeriodChart.exists_lin_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:32.003802+00:00
-- url     : https://prove2.me/submissions/8187e78c-34f1-43d2-8c1d-c327e53e2e70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.PeriodChart
theorem _root_.solution (T : V →+ V) (hT : ∀ (r : ℝ) z, T ((r : ℂ) • z) = (r : ℂ) • T z) :
    ∃ (A : V →ₗ[ℂ] V) (C : V →ₗ⋆[ℂ] V), ∀ z, T z = A z + C z := by
  have hTI : ∀ z, T (Complex.I • Complex.I • z) = -T z := by
    intro z
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul, map_neg]
  have hTc : ∀ (c : ℂ) z, T (c • z) = (c.re : ℂ) • T z + (c.im : ℂ) • T (Complex.I • z) := by
    intro c z
    conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul, map_add, hT, hT]
  refine ⟨{ toFun := fun z => (1 / 2 : ℂ) • (T z - Complex.I • T (Complex.I • z)),
            map_add' := ?_, map_smul' := ?_ },
          { toFun := fun z => (1 / 2 : ℂ) • (T z + Complex.I • T (Complex.I • z)),
            map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    simp only [smul_add, map_add]
    module
  · intro c z
    simp only [RingHom.id_apply]
    rw [hTc c z, smul_comm Complex.I c z, hTc c (Complex.I • z), hTI]
    conv_rhs => rw [← Complex.re_add_im c]
    match_scalars <;>
      first
      | ring1
      | linear_combination ((c.im : ℂ) / 2) * Complex.I_sq
  · intro x y
    simp only [smul_add, map_add]
    module
  · intro c z
    rw [hTc c z, smul_comm Complex.I c z, hTc c (Complex.I • z), hTI]
    conv_rhs => rw [← Complex.re_add_im c]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    match_scalars <;>
      first
      | ring1
      | linear_combination ((c.im : ℂ) / 2) * Complex.I_sq
  · intro z
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    module
end GlobalTheory.PeriodChart
