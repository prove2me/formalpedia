-- Prove2me | solution 1 for GlobalTheory.genericSection_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:40:31.880638+00:00
-- url     : https://prove2.me/submissions/93b2afee-7419-43ac-b8f8-e94649a9564a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightIntegralEstimates
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GenericSectionInjectiveOfAxH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.AlgT
namespace GlobalTheory
theorem _root_.solution {F : Type} [Field F] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → F) :
    ReciprocityTheory.MultiplicativeHeights.sImage (D := D) x = sImg (D := D) j₀ x ∘
      (Equiv.prodCongr (Equiv.refl (Fin (D + 1))) (Fin.cycleRange j₀).symm) := by
  funext p
  obtain ⟨i, j⟩ := p
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_zero]
  · simp [ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_succ]
end GlobalTheory
