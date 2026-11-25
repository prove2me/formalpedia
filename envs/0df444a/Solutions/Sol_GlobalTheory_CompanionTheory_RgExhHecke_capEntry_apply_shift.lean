-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.capEntry_apply_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:45.949401+00:00
-- url     : https://prove2.me/submissions/3a558069-08aa-4616-a8fd-f4dbe5558072

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
namespace GlobalTheory.CompanionTheory.RgExhHecke
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (x : ℂ) (a b : Fin n) (v : V) :
    capEntry E x a b v = capEntry E (x - 1) a b v + if b = a then v else 0 := by
  unfold capEntry
  by_cases h : a = b
  · subst h
    simp [Module.algebraMap_end_apply, sub_smul, add_assoc]
  · simp [h, Ne.symm h]
end GlobalTheory.CompanionTheory.RgExhHecke
