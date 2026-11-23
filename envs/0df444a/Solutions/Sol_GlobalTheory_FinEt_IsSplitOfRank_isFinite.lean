-- Prove2me | solution 1 for GlobalTheory.FinEt.IsSplitOfRank.isFinite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:18.346335+00:00
-- url     : https://prove2.me/submissions/9215d347-b89d-42e7-b202-a56a48f9962e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_isIso_coprodDesc
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_zero_iff
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_succ
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_exists_of_succ

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
theorem _root_.solution {X S : Scheme.{u}} {p : X ⟶ S} {n : ℕ} (h : IsSplitOfRank p n) :
    IsFinite p := by
  induction n generalizing X with
  | zero =>
    have := (isSplitOfRank_zero_iff p).mp h
    infer_instance
  | succ n ih =>
    obtain ⟨σ, _, V, hσ, hV, h'⟩ := h.exists_of_succ
    have := ih h'
    have := isIso_coprodDesc σ V.ι hV
    have e : coprod.desc σ V.ι ≫ p = coprod.desc (𝟙 S) (V.ι ≫ p) := by
      rw [coprod.desc_comp, hσ]
    rw [← IsIso.inv_hom_id_assoc (coprod.desc σ V.ι) p, e]
    infer_instance
end IsSplitOfRank
end GlobalTheory.FinEt
