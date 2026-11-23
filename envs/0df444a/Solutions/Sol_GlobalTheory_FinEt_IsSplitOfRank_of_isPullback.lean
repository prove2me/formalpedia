-- Prove2me | solution 1 for GlobalTheory.FinEt.IsSplitOfRank.of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:09.92787+00:00
-- url     : https://prove2.me/submissions/251a8de4-57ec-4c52-bff1-94d97dae557a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_range_of_isPullback
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_iff
import Theorems.Thm_GlobalTheory_FinEt_isPullback_section

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}
namespace GlobalTheory.FinEt
namespace IsSplitOfRank
theorem _root_.solution {X S X' S' : Scheme.{u}} {a : X' ⟶ X} {q : X' ⟶ S'}
    {p : X ⟶ S} {t : S' ⟶ S} (H : IsPullback a q p t) {n : ℕ} (h : IsSplitOfRank p n) :
    IsSplitOfRank q n := by
  rw [isSplitOfRank_iff] at h ⊢
  obtain ⟨s, hs, ho, hx⟩ := h
  refine ⟨fun i ↦ H.lift (t ≫ s i) (𝟙 S') (by simp [hs]), fun i ↦ H.lift_snd _ _ _,
    fun i ↦ MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_section H (s i) (hs i)).flip (ho i), fun x ↦ ?_⟩
  simp only [range_of_isPullback (isPullback_section H _ (hs _)), Set.mem_preimage]
  exact hx (a x)
end IsSplitOfRank
end GlobalTheory.FinEt
