-- Prove2me | solution 1 for GlobalTheory.Per.Sen.finrank_span_image_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:07:05.050776+00:00
-- url     : https://prove2.me/submissions/ef59cbaf-aeda-463e-9b98-38eee8377cf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AntitoneFiltrationExistsAdaptedLinearIndepSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankSpanImageEqCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.Per GlobalTheory.Per.Sen
namespace GlobalTheory.Per.Sen
theorem _root_.solution {L M : Type} [Field L] [AddCommGroup M] [Module L M] {m : ℕ}
    (d : Fin m → M) (hd : LinearIndependent L d) (p : Fin m → Prop) [DecidablePred p] :
    Module.finrank L (Submodule.span L (d '' {i | p i})) = (Finset.univ.filter p).card := by
  have h := finrank_span_eq_card (hd.comp (Subtype.val : {i // p i} → Fin m) Subtype.val_injective)
  rw [Fintype.card_subtype] at h
  rw [show d '' {i | p i} = Set.range (d ∘ (Subtype.val : {i // p i} → Fin m)) by
    ext x; simp [Set.mem_image, Set.mem_range]]
  exact h
end GlobalTheory.Per.Sen
