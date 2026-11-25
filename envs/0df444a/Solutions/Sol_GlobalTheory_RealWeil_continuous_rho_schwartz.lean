-- Prove2me | solution 1 for GlobalTheory.RealWeil.continuous_rho_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:42:30.872219+00:00
-- url     : https://prove2.me/submissions/70c07bd8-daa8-4dc2-859b-642a25b55722

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousRhoApply
import Theorems.Thm_GlobalTheory_RealWeil_continuous_inner_rho_schwartz
import Theorems.Thm_GlobalTheory_RealWeil_coeFn_rho
import Theorems.Thm_GlobalTheory_RealWeil_coe_rhoSch


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
open scoped Matrix Real RealInnerProductSpace InnerProductSpace
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (f : Sch l) : Continuous fun w : l ⊕ l → ℝ => rho w (f.toLp 2) := by
  rw [continuous_iff_continuousAt]
  intro w₀
  set v : L2 l := f.toLp 2 with hv
  set g : L2 l := (rhoSch w₀ f).toLp 2 with hg
  have h0 : rho w₀ v = g := by
    refine Lp.ext ?_
    filter_upwards [coeFn_rho w₀ (f.toLp 2), rhoFun_congr w₀ (f.coeFn_toLp 2 volume),
      (rhoSch w₀ f).coeFn_toLp 2 volume] with x h1 h2 h3
    rw [h1, h2, h3, coe_rhoSch]
  have hsq : ∀ w, ‖rho w v - rho w₀ v‖ ^ 2 =
      2 * ‖v‖ ^ 2 - 2 * (⟪g, rho w v⟫_ℂ).re := by
    intro w
    rw [@norm_sub_sq ℂ, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, inner_re_symm, h0,
      RCLike.re_to_complex]
    ring
  have hc : Continuous fun w => ‖rho w v - rho w₀ v‖ ^ 2 := by
    simp only [hsq]
    exact continuous_const.sub (continuous_const.mul (continuous_re.comp (continuous_inner_rho_schwartz (rhoSch w₀ f) f)))
  have ht := hc.tendsto w₀
  simp only [sub_self, norm_zero] at ht
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto _).comp ht
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
end GlobalTheory.RealWeil
