-- Prove2me | solution 1 for GlobalTheory.Phase.VacShape.vac_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:10:32.994523+00:00
-- url     : https://prove2.me/submissions/5eeac297-25cc-4ada-abd6-71df6fd6949a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SelfDualVacuumGaussianShapeRootOfUnityPhases
import Theorems.Thm_GlobalTheory_SW_Vac_fixed_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.VacShape
open GlobalTheory.SW.Vac
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
  {A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)} {ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ}
  {φ : Matrix κ ι ℚ → ℂ}
namespace GlobalTheory.Phase.VacShape
theorem _root_.solution (h : VacS A ε φ) (u : ℂ) : VacS A ε (u • φ) := by
  refine ⟨h.fg, h.dual, h.norm, h.semi, h.ord, ?_, fun y hy => ?_⟩
  · obtain ⟨R, hR, h1, h2⟩ := h.sb
    refine ⟨R, hR, fun x hx => h1 x fun e => hx (by simp [e]), fun x z hz => ?_⟩
    simp only [Pi.smul_apply, h2 x z hz]
  · rw [fixed_iff]
    intro x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm, (fixed_iff ε y φ).1 (h.fix y hy) x]
end GlobalTheory.Phase.VacShape
