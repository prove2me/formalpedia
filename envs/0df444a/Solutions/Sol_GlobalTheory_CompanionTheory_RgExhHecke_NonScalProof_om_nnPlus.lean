-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.om_nnPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:23:38.607716+00:00
-- url     : https://prove2.me/submissions/a766e321-d55c-4467-afa7-4718f5403a5a

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeNonScalar
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capelli_expand_plus


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
namespace GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
theorem _root_.solution {m : ℕ} (X : GMod (m + 1)) (y : Fin (m + 1) → ℂ) (x : ℂ) (v : X.V) :
    om X (nnPlus X.E y x v) + x • nnPlus X.E y x v = fun b => y b • capelliC X.E x v := by
  have hE' : GlRelR X.E := X.gl
  funext b
  have key : ∀ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
      X.E d b (cminor X.E d.succAbove c.succAbove (x - 1) v) +
      (x * (-1 : ℂ) ^ ((b : ℕ) + (c : ℕ))) • cminor X.E b.succAbove c.succAbove (x - 1) v =
      (if b = c then capelliC X.E x else 0) v := by
    intro c
    have h := LinearMap.congr_fun (capelli_expand_plus X.E hE' x b c) v
    rw [LinearMap.sum_apply] at h
    simp only [LinearMap.smul_apply, Module.End.mul_apply, capEntry, LinearMap.add_apply, smul_add,
      Finset.sum_add_distrib] at h
    have h2 : ∑ z : Fin (m + 1), ((-1 : ℂ) ^ ((z : ℕ) + (c : ℕ))) •
        (if z = b then algebraMap ℂ (Module.End ℂ X.V) x else 0) (cminor X.E z.succAbove c.succAbove (x - 1) v) =
        (x * (-1 : ℂ) ^ ((b : ℕ) + (c : ℕ))) • cminor X.E b.succAbove c.succAbove (x - 1) v := by
      rw [Finset.sum_eq_single b]
      · simp [Module.algebraMap_end_apply, smul_smul, mul_comm]
      · intro d _ hd; simp [hd]
      · simp
    rw [h2] at h
    exact h
  have hR : y b • capelliC X.E x v = ∑ c, y c • (if b = c then capelliC X.E x else 0) v := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  show om X (nnPlus X.E y x v) b + x • nnPlus X.E y x v b = y b • capelliC X.E x v
  rw [hR, om_apply]
  simp only [nnPlus, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← key c, smul_add, Finset.smul_sum]
  simp only [smul_smul]
  rw [mul_left_comm]
end GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
