-- Prove2me | solution 1 for GlobalTheory.AnDim.immersedPieces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:43:34.334154+00:00
-- url     : https://prove2.me/submissions/24324622-0048-4b2f-b712-7ac434776ccb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
import Theorems.Thm_GlobalTheory_AnDim_hasHoloImm_of_regularLocus
import Theorems.Thm_GlobalTheory_AnDim_hasHoloImm_iff
import Theorems.Thm_GlobalTheory_LogResInt_isAnalyticSubset_inter


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.AnDim
theorem _root_.solution (h : Published.AnalyticSetDimension) (d : ℕ) (X : Type) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (A : FinHolAtlas d X) :
    (∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty →
      ¬ HasHoloImm A Z (n + 1)) ∧
    (∀ (C S : Set X) (k : ℕ), IsIrreducibleAnalytic A C → A.IsAnalyticSubset S → ¬ C ⊆ S →
      HasHoloImm A (C ∩ S) k → HasHoloImm A C (k + 1)) ∧
    (∀ S : Set X, A.IsAnalyticSubset S →
      {C | IsIrreducibleComponent A S C}.Finite ∧ S = ⋃₀ {C | IsIrreducibleComponent A S C}) := by
  obtain ⟨-, h2, h3, h4⟩ := h d X A
  refine ⟨fun Z n hZ hn hc => ?_, fun C S k hC hS hCS hk => ?_, h4⟩
  · have h5 := (hasHoloImm_iff h hZ.1).1 hc
    rw [h2 Z n hZ hn] at h5
    have : n + 1 ≤ n := by exact_mod_cast h5
    omega
  · have h5 := ((hasHoloImm_iff h (isAnalyticSubset_inter hC.1 hS)).1 hk).trans_lt (h3 C S hC hS hCS)
    obtain ⟨n, hn, hlt⟩ : ∃ n : ℕ, (regularLocus A C n).Nonempty ∧ (k : WithBot ℕ∞) < n := by
      obtain ⟨n, hn⟩ := lt_iSup_iff.1 h5
      obtain ⟨hn', hn⟩ := lt_iSup_iff.1 hn
      exact ⟨n, hn', hn⟩
    exact hasHoloImm_of_regularLocus (by exact_mod_cast hlt) hn
end GlobalTheory.AnDim
