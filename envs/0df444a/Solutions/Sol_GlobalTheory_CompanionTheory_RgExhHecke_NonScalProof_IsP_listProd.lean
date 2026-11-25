-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.IsP.listProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:04:52.417414+00:00
-- url     : https://prove2.me/submissions/a6b70ce5-5954-4f8b-943b-3586d3890cf5

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeNonScalar
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_IsP_const
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_IsP_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
namespace IsP
theorem _root_.solution (l : List (ℂ → A)) (h : ∀ f ∈ l, IsP f) :
    IsP (fun t => (l.map fun f => f t).prod) := by
  induction l with
  | nil => simpa using IsP.const (1 : A)
  | cons f l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h f (by simp)).mul (ih fun g hg => h g (by simp [hg]))
end IsP
end GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
