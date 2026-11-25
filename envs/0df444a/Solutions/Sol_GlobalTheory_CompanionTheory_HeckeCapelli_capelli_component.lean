-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeCapelli.capelli_component
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:46.493674+00:00
-- url     : https://prove2.me/submissions/f22ddfd6-77c2-4e62-a5cf-5d3c1cb30ed8

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEqualityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaMinor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capelliExpand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCapelli
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor capelliC capEntry capelliExpand)
namespace GlobalTheory.CompanionTheory.HeckeCapelli
theorem _root_.solution {m : ℕ} (X : GMod (m + 1)) (x : ℂ) (f : Fin (m + 1) → X.V) (b : Fin (m + 1)) :
    ∑ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        capEntry X.E x d b (cminor X.E d.succAbove c.succAbove (x - 1) (f c)) = capelliC X.E x (f b) := by
  have key := (capelliExpand (Module.End ℂ X.V) m X.E x X.gl).1 b
  have h : ∀ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        capEntry X.E x d b (cminor X.E d.succAbove c.succAbove (x - 1) (f c)) =
      if b = c then capelliC X.E x (f c) else 0 := by
    intro c
    have := LinearMap.congr_fun (key c) (f c)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this
    rw [this]
    split_ifs <;> simp
  simp only [h]
  simp
end GlobalTheory.CompanionTheory.HeckeCapelli
