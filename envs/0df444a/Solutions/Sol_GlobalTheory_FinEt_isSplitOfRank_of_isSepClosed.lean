-- Prove2me | solution 1 for GlobalTheory.FinEt.isSplitOfRank_of_isSepClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:25:52.243961+00:00
-- url     : https://prove2.me/submissions/b5df35eb-c29b-4027-98fc-cfaa89b2936d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_pullback_snd
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_of_isPullback_of_isPullback
import Theorems.Thm_GlobalTheory_FinEt_exists_isPullback_isSplitOfRank
import Theorems.Thm_GlobalTheory_FinEt_exists_section_of_isSepClosed

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
theorem _root_.solution {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsFinite p] [Etale p] (s : Spec (.of k)) :
    IsSplitOfRank p (p.finrank s) := by
  obtain ⟨S', X', t, a, q, h1, h2, h3, H, hq⟩ := exists_isPullback_isSplitOfRank (p.finrank s) p
    fun s' ↦ by rw [Subsingleton.elim s' s]
  have : Nonempty S' := ⟨(t.surjective s).choose⟩
  obtain ⟨σ, hσ⟩ := exists_section_of_isSepClosed t
  have G := (IsPullback.of_hasPullback q σ).paste_horiz H
  rw [hσ] at G
  exact (hq.pullback_snd σ).of_isPullback_of_isPullback G IsPullback.of_id_fst
end GlobalTheory.FinEt
