-- Prove2me | solution 1 for GlobalTheory.SectionSum.exists_ae_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:36:00.621806+00:00
-- url     : https://prove2.me/submissions/6b35d65b-8eff-415a-ba6c-2d5e3b6f50be

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AemeasurableFinsumSection

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
theorem _root_.solution {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (hμ : μ ≠ 0)
    (D : ℕ) (p : (Fin (D + 1) → α) → Prop)
    (hp : ∀ᵐ t ∂(Measure.pi fun _ : Fin (D + 1) => μ), p t) :
    ∃ t₀ : α, ∀ᵐ t ∂(Measure.pi fun _ : Fin D => μ), p (Fin.cons t₀ t) := by
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (D + 1) => μ) 0).symm
  have h1 := hm.quasiMeasurePreserving.ae hp
  have h2 := Measure.ae_ae_of_ae_prod h1
  haveI : (ae μ).NeBot := ae_neBot.2 hμ
  obtain ⟨t₀, ht₀⟩ := h2.exists
  refine ⟨t₀, ht₀.mono fun t ht => ?_⟩
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using ht
end GlobalTheory.SectionSum
