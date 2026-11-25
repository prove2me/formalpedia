-- Prove2me | solution 1 for GlobalTheory.FinEt.IsSplitOfRank.finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:42:36.607908+00:00
-- url     : https://prove2.me/submissions/dc124390-4ab0-4965-8fa1-8d0fb1117c0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_finrank_eq_add
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_zero_iff
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_succ
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_exists_of_succ
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_etale
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_isFinite

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
theorem _root_.solution {X S : Scheme.{u}} {p : X ⟶ S} {n : ℕ} (h : IsSplitOfRank p n)
    (s : S) : p.finrank s = n := by
  have := h.isFinite
  have := h.etale
  induction n generalizing X with
  | zero =>
    have := (isSplitOfRank_zero_iff p).mp h
    have := finrank_eq_add (𝟙 X) (𝟙 X) (Subsingleton.elim _ _) p s
    rw [Category.id_comp] at this
    omega
  | succ n ih =>
    obtain ⟨σ, _, V, hσ, hV, h'⟩ := h.exists_of_succ
    rw [finrank_eq_add σ V.ι hV p s, hσ, Scheme.Hom.finrank_eq_one_of_isIso (𝟙 S),
      ih h' h'.isFinite h'.etale, Pi.one_apply, add_comm]
end IsSplitOfRank
end GlobalTheory.FinEt
