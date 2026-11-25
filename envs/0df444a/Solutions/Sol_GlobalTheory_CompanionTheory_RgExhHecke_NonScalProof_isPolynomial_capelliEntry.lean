-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.isPolynomial_capelliEntry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:58.039599+00:00
-- url     : https://prove2.me/submissions/1d3bb45a-a64b-4cb8-971e-68cd0ca4b2b3

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeNonScalar
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_IsP_const
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_IsP_lin

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
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (x₀ : ℂ) (a b : Fin n) :
    IsP (fun t : ℂ => capEntry E (x₀ + t) a b) := by
  by_cases h : a = b
  · have := IsP.lin (E a b + algebraMap ℂ A x₀) (1 : A)
    convert this using 2 with t
    simp [capEntry, h, map_add, add_assoc]
  · have := IsP.const (E a b)
    convert this using 2 with t
    simp [capEntry, h]
end GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
