-- Prove2me | solution 1 for GlobalTheory.NB.bHyp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:05:23.277182+00:00
-- url     : https://prove2.me/submissions/9a3b68c6-d6bf-4fdb-b074-bce90754f7b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_RoundDown
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_OfKillsOne
import Theorems.Thm_GlobalTheory_NB_typed_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB
variable {l : ℕ} {O : Type} [CommRing O] [IsDomain O] {R : Fr l O} {n r₁ r : ℕ}
variable {S₁ : Sys R n r₁} {S : Sys R n r} {F : Hom S₁ S}
namespace GlobalTheory.NB
theorem _root_.solution [NeZero n] {up : ZMod n → Bool} {sz : ZMod n → ℕ} {b w Sn η m h : ℕ}
    {A ρ : ZMod n → ℕ} :
    BHyp F up sz b w Sn η m h A ρ ↔ BSet F up sz b w Sn η m h ∧ CutBounds F sz w Sn η h A ρ :=
  ⟨fun H => ⟨⟨H.isA, H.l_ge, Nat.pos_of_ne_zero (NeZero.ne n), (typed_iff.1 H.typed).1, H.w_pos,
      H.small, H.thick_or, H.some_thin, H.h_def⟩,
      H.killX, H.killL, H.killCut, H.A_le, H.a_le, H.A_next, H.A_cut⟩,
    fun ⟨H, h1, h2, h3, h4, h5, h6, h7⟩ => ⟨H.isA, H.l_ge, typed_iff.2 ⟨H.typed, fun i => ⟨_, h2 i⟩⟩,
      H.w_pos, H.small, H.thick_or, H.some_thin, H.h_def, h1, h2, h3, h4, h5, h6, h7⟩⟩
end GlobalTheory.NB
