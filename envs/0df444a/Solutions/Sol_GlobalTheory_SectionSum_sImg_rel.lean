-- Prove2me | solution 1 for GlobalTheory.SectionSum.sImg_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:33:59.788491+00:00
-- url     : https://prove2.me/submissions/a9f8e76d-f4ce-4bce-b21b-544dd3cae6d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AemeasurableFinsumSection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sac_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sac_succAbove


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.SectionSum
open MvPolynomial MeasureTheory
namespace GlobalTheory.SectionSum
theorem _root_.solution {Ω : Type} [Field Ω] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → Ω) (i : Fin D) :
    sImg (D := D) j₀ x (i.succ, j₀) +
      ∑ k, sImg (D := D) j₀ x (i.succ, j₀.succAbove k) * algebraMap Ω (OmS Ω D N) (x k) = 0 := by
  have hC : ∀ a : Ω, algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (C a) =
      algebraMap Ω (OmS Ω D N) a := fun a => by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simp only [sImg, sac_self, sac_succAbove, Fin.succ_ne_zero, if_false,
    ↓reduceIte, map_neg, map_sum, map_mul, hC]
  exact neg_add_cancel _
end GlobalTheory.SectionSum
