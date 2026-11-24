-- Prove2me | solution 1 for GlobalTheory.Published.SvN.eventually_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:54:11.869828+00:00
-- url     : https://prove2.me/submissions/d860a192-fb8f-4b04-8e02-4cba91834002

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_eq_one_of_pow_near
import Theorems.Thm_GlobalTheory_Published_SvN_isCompact_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.Published.SvN
theorem _root_.solution {ψ : AddChar F ℂ} (hψ : Continuous ψ) : ∀ᶠ z in 𝓝 (0 : F), ∀ o ∈ 𝒪[F], ψ (o * z) = 1 := by
  have h1 : ∀ᶠ z in 𝓝 (0 : F), ∀ o ∈ (𝒪[F] : Set F), ‖ψ (o * z) - 1‖ < 1 / 2 := by
    refine isCompact_int.eventually_forall_of_forall_eventually fun o _ => ?_
    have hc : Continuous fun z : F × F => ‖ψ (z.2 * z.1) - 1‖ := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
  filter_upwards [h1] with z hz o ho
  refine eq_one_of_pow_near fun n => ?_
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ← mul_assoc]
  exact hz _ (mul_mem (natCast_mem _ n) ho)
end GlobalTheory.Published.SvN
