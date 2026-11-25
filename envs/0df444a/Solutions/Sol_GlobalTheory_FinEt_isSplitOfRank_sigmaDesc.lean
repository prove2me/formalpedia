-- Prove2me | solution 1 for GlobalTheory.FinEt.isSplitOfRank_sigmaDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:58:25.182805+00:00
-- url     : https://prove2.me/submissions/3aaaafc2-6f5d-42f9-afdd-be507f606965

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed

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
theorem _root_.solution (S : Scheme.{u}) (n : ℕ) :
    IsSplitOfRank (Sigma.desc fun _ : Fin n ↦ 𝟙 S) n :=
  ⟨fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i, fun i ↦ by simp, ⟨coproductIsCoproduct _⟩⟩
end GlobalTheory.FinEt
