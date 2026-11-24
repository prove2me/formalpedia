-- Prove2me | solution 1 for GlobalTheory.ExplicitRect.logDeriv_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:49:12.518798+00:00
-- url     : https://prove2.me/submissions/ea429898-f248-4b0c-8c67-0590aa6fec6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AnalyticAtDslope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExplicitRect
namespace GlobalTheory.ExplicitRect
theorem _root_.solution {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      deriv (LFunction χ) s / LFunction χ s = (if N = 1 then -1 else 0) / (s - 1) + g s := by
  by_cases hN : N = 1
  · subst hN
    obtain rfl : χ = 1 := DirichletCharacter.level_one χ
    have hZd := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
    have hZa : AnalyticAt ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) 1 := hZd.analyticAt 1
    have hZ1 := DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1
    refine ⟨fun s => deriv (DirichletCharacter.LFunctionTrivChar₁ 1) s /
      DirichletCharacter.LFunctionTrivChar₁ 1 s, hZa.deriv.div hZa hZ1, ?_⟩
    have hne : ∀ᶠ s in 𝓝 (1 : ℂ), DirichletCharacter.LFunctionTrivChar₁ 1 s ≠ 0 :=
      hZa.continuousAt.eventually_ne hZ1
    filter_upwards [nhdsWithin_le_nhds hne, self_mem_nhdsWithin] with s hZs hs1
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hLeq : LFunction (1 : DirichletCharacter ℂ 1) =ᶠ[𝓝 s]
        fun z => DirichletCharacter.LFunctionTrivChar₁ 1 z / (z - 1) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
      have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz
      rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz]
      field_simp
    have hd : HasDerivAt (fun z => DirichletCharacter.LFunctionTrivChar₁ 1 z / (z - 1))
        ((deriv (DirichletCharacter.LFunctionTrivChar₁ 1) s * (s - 1) -
          DirichletCharacter.LFunctionTrivChar₁ 1 s * 1) / (s - 1) ^ 2) s :=
      (hZd s).hasDerivAt.div ((hasDerivAt_id' s).sub_const 1) hs1'
    rw [hLeq.deriv_eq, hLeq.eq_of_nhds, hd.deriv, if_pos rfl]
    field_simp
    ring
  · have hχ1 : χ ≠ 1 := by
      rintro rfl
      rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at hχ
      exact hN hχ.symm
    have hLa : AnalyticAt ℂ (LFunction χ) 1 := (DirichletCharacter.differentiable_LFunction hχ1).analyticAt 1
    have hL1 := DirichletCharacter.LFunction_apply_one_ne_zero hχ1
    refine ⟨fun s => deriv (LFunction χ) s / LFunction χ s, hLa.deriv.div hLa hL1,
      Filter.Eventually.of_forall fun s => ?_⟩
    simp only [hN, if_false, zero_div, zero_add]
end GlobalTheory.ExplicitRect
