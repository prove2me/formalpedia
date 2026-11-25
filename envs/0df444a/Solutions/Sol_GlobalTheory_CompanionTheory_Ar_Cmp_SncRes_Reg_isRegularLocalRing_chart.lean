-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.isRegularLocalRing_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:12:55.014924+00:00
-- url     : https://prove2.me/submissions/891be1cd-586a-4367-a8a4-84753f2a93ef

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRing
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_card_le_finrank_jacSpanAt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_rep_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm
import Theorems.Thm_ReciprocityTheory_AnForm_R_finrank_cotangentSpace_locAt
import Theorems.Thm_ReciprocityTheory_AnForm_R_locAt_isLocalRing_isNoetherian
import Theorems.Thm_ReciprocityTheory_AnForm_R_mem_conePts_iff_chartIdeal
import Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_locAt_chart
import Theorems.Thm_ReciprocityTheory_CA_DepthGE_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_CA_IsCM_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomogIdeal_pC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_pcEquidim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
theorem _root_.solution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) ∧ ringKrullDim (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) = e := by
  intro K _ ι _ Ω _ _ y e J hP hsnc p x hx
  classical
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hP.2.1.2.1
  have hz := rep_mem x
  have hw := (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPh p (rep x) hx).1 hz
  have hy : ∀ k, y ⟨k, p k⟩ ≠ 0 := by
    intro k h0
    have hX : (X ⟨k, p k⟩ : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0]
      simp
    have h1 := hz.2 _ (Ideal.subset_span ⟨_, hX, rfl⟩)
    rw [map_X, eval_X] at h1
    exact hx k h1
  obtain ⟨hloc, hnoeth⟩ := ReciprocityTheory.AnForm.R.locAt_isLocalRing_isNoetherian _ _ hw
  have hd := ReciprocityTheory.AnForm.R.ringKrullDim_locAt_chart _ hPh e (pcEquidim K ι _ e hP) p _ hw
  have hcot := ReciprocityTheory.AnForm.R.finrank_cotangentSpace_locAt
    (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p) (ReciprocityTheory.AnForm.R.affCoord p (rep x))
  have hrank := card_le_finrank_jacSpanAt K ι Ω y e J hsnc p hy _ hw
  have hreg : IsRegularLocalRing (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p)
      (ReciprocityTheory.AnForm.R.affCoord p (rep x))) := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hd]
    have : Module.finrank (IsLocalRing.ResidueField (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p)
        (ReciprocityTheory.AnForm.R.affCoord p (rep x)))) (IsLocalRing.CotangentSpace (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p)
        (ReciprocityTheory.AnForm.R.affCoord p (rep x)))) ≤ e := by omega
    exact_mod_cast this
  exact ⟨IsRegularLocalRing.of_ringEquiv (ReciprocityTheory.AnForm.R.locAtEquiv _ _),
    (ringKrullDim_eq_of_ringEquiv (ReciprocityTheory.AnForm.R.locAtEquiv _ _)).symm.trans hd⟩
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
