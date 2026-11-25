-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.minor_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:07:53.346841+00:00
-- url     : https://prove2.me/submissions/6fe04d5b-3388-4167-9031-b8e0487ff665

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_WhittakerZeroStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeRankOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_succ_col


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
theorem _root_.solution (i : Fin (q + 2)) (l : Fin (q + 1)) :
    cminor E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) =
      ∑ k : Fin (q + 1), ((-1 : ℂ) ^ (k : ℕ)) •
        capEntry E (x - 1) (R (i.succAbove k)) (C 0) (dbl E R C x f i k l) := by
  rw [cminor_succ_col]
  have h0 : (C ∘ l.succ.succAbove) 0 = C 0 := by simp
  have h1 : (C ∘ l.succ.succAbove) ∘ Fin.succ = (C ∘ Fin.succ) ∘ l.succAbove := by
    funext t
    simp [Function.comp, Fin.succ_succAbove_succ]
  rw [h0, h1]
  simp [dbl, LinearMap.sum_apply, Module.End.mul_apply]
end GlobalTheory.CompanionTheory.RgExhHecke
