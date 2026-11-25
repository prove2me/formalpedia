-- Prove2me | solution 1 for GlobalTheory.RealWeil.SchrFamily.continuous_rhoSch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:15:47.2358+00:00
-- url     : https://prove2.me/submissions/ee82e484-3cfc-4275-b58c-db37016978ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepSchwartzPolynomialBound
import Theorems.Thm_GlobalTheory_RealWeil_SchrFamily_tendsto_rhoSch_zero
import Theorems.Thm_GlobalTheory_RealWeil_SchrFamily_rhoSch_rhoSch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil Filter Topology
open scoped SchwartzMap RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.SchrFamily
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil.SchrFamily
theorem _root_.solution (g : Sch l) : Continuous fun w => rhoSch w g := by
  refine continuous_iff_continuousAt.2 fun w₀ => ?_
  set c : (l ⊕ l → ℝ) → ℂ := fun u => Complex.exp (((Real.pi * sympl w₀ u : ℝ) : ℂ) * Complex.I) with hcdef
  have hs : Continuous fun u : l ⊕ l → ℝ => sympl w₀ u := by
    have e : (fun u : l ⊕ l → ℝ => sympl w₀ u) =
        fun u => ⟪pPart w₀, qCLM l u⟫ - ⟪qPart w₀, pCLM l u⟫ := rfl
    rw [e]
    exact (continuous_const.inner (qCLM l).continuous).sub (continuous_const.inner (pCLM l).continuous)
  have hc : Continuous c := by
    rw [hcdef]
    fun_prop
  have h1 : Tendsto (fun u => (c u)⁻¹ • rhoSch w₀ (rhoSch u g)) (𝓝 0) (𝓝 ((c 0)⁻¹ • rhoSch w₀ g)) :=
    ((hc.tendsto 0).inv₀ (Complex.exp_ne_zero _)).smul
      (((rhoSch w₀).continuous.tendsto g).comp (tendsto_rhoSch_zero g))
  have hq0 : qPart (0 : l ⊕ l → ℝ) = 0 := rfl
  have hp0 : pPart (0 : l ⊕ l → ℝ) = 0 := rfl
  have hc0 : c 0 = 1 := by simp [hcdef, sympl, hq0, hp0]
  have e : ∀ u, (c u)⁻¹ • rhoSch w₀ (rhoSch u g) = rhoSch (w₀ + u) g := fun u => by
    rw [rhoSch_rhoSch, inv_smul_smul₀ (Complex.exp_ne_zero _)]
  simp only [e, hc0, inv_one, one_smul] at h1
  have h3 : Tendsto (fun w => w - w₀) (𝓝 w₀) (𝓝 0) := (continuous_sub_right w₀).tendsto' _ _ (sub_self _)
  refine (h1.comp h3).congr fun w => ?_
  simp
end GlobalTheory.RealWeil.SchrFamily
