-- Prove2me | solution 1 for GlobalTheory.RealWeil.continuous_rho_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:18:54.666617+00:00
-- url     : https://prove2.me/submissions/12adaf95-246e-47dd-8766-97030d8a2865

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousRhoApply
import Theorems.Thm_GlobalTheory_RealWeil_continuous_rho_schwartz

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
theorem _root_.solution : Continuous fun x : L2 l × (l ⊕ l → ℝ) => rho x.2 x.1 := by
  have hd : Dense (Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (EuclideanSpace ℝ l)))) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  exact continuous_prod_of_dense_continuous_lipschitzWith (fun x : L2 l × (l ⊕ l → ℝ) => rho x.2 x.1) 1 hd
    (by rintro _ ⟨f, rfl⟩; exact continuous_rho_schwartz f) fun w => (rho w).lipschitz
end GlobalTheory.RealWeil
