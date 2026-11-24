-- Prove2me | solution 1 for GlobalTheory.FinEt.exists_iso_sigma_of_isSepClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:45:15.983339+00:00
-- url     : https://prove2.me/submissions/96a9992a-1c3a-499b-99a0-ec0f05a8191d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_iff_exists_iso
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_of_isSepClosed

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
    (p : X ⟶ Spec (.of k)) [IsFinite p] [Etale p] :
    ∃ (n : ℕ) (e : (∐ fun _ : Fin n ↦ Spec (.of k)) ≅ X),
      e.hom ≫ p = Sigma.desc fun _ : Fin n ↦ 𝟙 (Spec (.of k)) := by
  obtain ⟨s⟩ : Nonempty (Spec (.of k)) := inferInstance
  exact ⟨_, (isSplitOfRank_iff_exists_iso p _).mp (isSplitOfRank_of_isSepClosed p s)⟩
end GlobalTheory.FinEt
