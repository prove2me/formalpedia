-- Prove2me | solution 1 for GlobalTheory.IntegralFrameAllCompare.exists_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:35:14.003394+00:00
-- url     : https://prove2.me/submissions/d946773e-217a-4ee3-b6ff-6ee6cc3d50e4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_IntegralFrameAcquisition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_VVNonnegIffLeOne
import Theorems.Thm_GlobalTheory_IntegralFrameAllCompare_mem_range_iff
import Theorems.Thm_GlobalTheory_IntegralFrameAllCompare_vV_zpow
import Theorems.Thm_Formalism_L2_Pj_vV_mul
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameAllCompare
open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]
variable {W L : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
  [IsFractionRing W L]
namespace GlobalTheory.IntegralFrameAllCompare
theorem _root_.solution (i : K →+* L) (hi : ∀ a : V, i (algebraMap V K a) ∈ Set.range (algebraMap W L)) :
    ∃ r : ℕ, ∀ x : K, vV W (i x) = (r : ℤ) * vV V x := by
  have hnn : ∀ x : K, 0 ≤ vV V x → 0 ≤ vV W (i x) := fun x hx => by
    obtain ⟨a, rfl⟩ := (mem_range_iff x).2 hx
    exact (mem_range_iff _).1 (hi a)
  have hz : ∀ x : K, vV V x = 0 → vV W (i x) = 0 := fun x hx => by
    have h1 := hnn x hx.ge
    have h2 := hnn (x ^ (-1 : ℤ)) (by rw [vV_zpow, hx]; simp)
    rw [map_zpow₀, vV_zpow] at h2
    omega
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal V).valuation_exists_uniformizer K
  have hπ1 : vV V π = 1 := by simp [vV, valV, hπ]
  have hπ0 : π ≠ 0 := fun h => by simp [h, vV] at hπ1
  have hr := hnn π (by omega)
  refine ⟨(vV W (i π)).toNat, fun x => ?_⟩
  rw [Int.toNat_of_nonneg hr]
  by_cases hx : x = 0
  · simp [hx, vV]
  have h := hz (x * π ^ (-vV V x)) (by rw [vV_mul hx (zpow_ne_zero _ hπ0), vV_zpow, hπ1]; ring)
  rw [map_mul, map_zpow₀, vV_mul ((map_ne_zero i).2 hx) (zpow_ne_zero _ ((map_ne_zero i).2 hπ0)), vV_zpow] at h
  linarith
end GlobalTheory.IntegralFrameAllCompare
