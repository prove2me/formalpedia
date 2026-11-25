-- Prove2me | solution 1 for GlobalTheory.NB.cHyp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:05:26.858874+00:00
-- url     : https://prove2.me/submissions/3192da7f-5d46-4184-9e6f-ac5cca53a2cc

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
theorem _root_.solution [NeZero n] {b : ZMod n → ℕ} {Sn η m h : ℕ} :
    CHyp F b Sn η m h ↔ CSet F b Sn η m h ∧ (∀ i, ∃ a : ℕ, F.Kills i ((l : O⟦X⟧) ^ a)) ∧
      ∀ i, F.Kills i (R.E ^ aC l (h + η)) :=
  ⟨fun H => ⟨⟨H.isA, H.l_ge, Nat.pos_of_ne_zero (NeZero.ne n), H.even, (typed_iff.1 H.typed).1,
      H.big, H.half⟩, H.typed.good.2, H.kills⟩,
    fun H => ⟨H.1.isA, H.1.l_ge, H.1.even, typed_iff.2 ⟨H.1.typed, H.2.1⟩, H.1.big, H.1.half,
      H.2.2⟩⟩
end GlobalTheory.NB
