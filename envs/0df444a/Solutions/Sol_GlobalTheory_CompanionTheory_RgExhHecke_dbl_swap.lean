-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.dbl_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:50:38.358621+00:00
-- url     : https://prove2.me/submissions/b324b48a-3136-4016-a967-eaa76bc82411

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_WhittakerZeroStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeRankOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli CompanionTheory.RgExh
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke
variable {n : ℕ}
variable {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) {q : ℕ}
  (R C : Fin (q + 2) → Fin n) (x : ℂ) (f : Fin n → V) (d : Fin n)
namespace GlobalTheory.CompanionTheory.RgExhHecke
theorem _root_.solution (i : Fin (q + 2)) (k l : Fin (q + 1)) :
    dbl E R C x f (i.succAbove k) (k.predAbove i) l = dbl E R C x f i k l := by
  unfold dbl
  have : (R ∘ (i.succAbove k).succAbove) ∘ (k.predAbove i).succAbove = (R ∘ i.succAbove) ∘ k.succAbove := by
    funext t
    simp only [Function.comp, Fin.succAbove_succAbove_succAbove_predAbove]
  rw [this]
end GlobalTheory.CompanionTheory.RgExhHecke
