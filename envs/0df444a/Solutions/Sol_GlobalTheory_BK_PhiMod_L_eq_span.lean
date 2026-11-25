-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.L_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:31.219953+00:00
-- url     : https://prove2.me/submissions/93170fae-b1d6-497f-84cc-acf0449ba79b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_mem_tot
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_apply
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_mem_L

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
open GlobalTheory.BK.PhiMod
variable {O K l e a ι} (P : PhiMod O K l e a ι)
variable [Fact l.Prime]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution [NeZero a] : P.L = Submodule.span (A O K) (P.phi '' P.M) := by
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.2 ?_)
  · rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun τ _ => ?_
    have : P.Lcomp τ ≤ (Submodule.span (A O K) (P.phi '' P.M)).comap
        (LinearMap.single (A O K) (fun _ : ZMod a => ι → K⟦X⟧) τ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      refine Submodule.subset_span ⟨Pi.single (τ - 1) (Pi.single j 1), mem_tot.2 fun σ i => ?_, ?_⟩
      · simp only [Pi.single_apply]
        split_ifs
        · rw [Pi.single_apply]
          split_ifs
          exacts [one_mem _, zero_mem _]
        · exact zero_mem _
      · ext1 σ
        rw [phi_apply]
        by_cases h : σ = τ
        · subst h
          have : frobV l (Pi.single j (1 : K⟦X⟧)) = Pi.single j 1 := by
            ext1 i
            rw [frobV_apply, Pi.single_apply]
            split_ifs <;> simp
          simp [this]
        · simp [h]
    exact this (mem_tot.1 hv τ)
  · rintro _ ⟨v, hv, rfl⟩
    exact P.phi_mem_L hv
end GlobalTheory.BK.PhiMod
