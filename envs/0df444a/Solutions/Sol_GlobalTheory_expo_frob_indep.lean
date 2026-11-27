-- Prove2me | solution 1 for GlobalTheory.expo_frob_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:24.375335+00:00
-- url     : https://prove2.me/submissions/082ccbe4-d02d-425f-86b4-209697ec0c5b

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_TailInequalityEventually
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExpoFrobIndep
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_places_real_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool), ({ W with fr := fr, cj := cj } : Wts ι).Ok P ∧
      ∀ l : ℕ, l.Prime → W.WRange P l → ({ W with fr := fr, cj := cj } : Wts ι).coarseWeightBound P l = W.coarseWeightBound P l := by
  intro P hH hL ι _ _ W hW fr cj
  have hW' : ({ W with fr := fr, cj := cj } : Wts ι).Ok P :=
    { anti := hW.anti, what₂ := hW.what₂, block := hW.block, centre := hW.centre, window := hW.window,
      cloud := hW.cloud, low := hW.low, thick := hW.thick, other := hW.other }
  refine ⟨hW', ?_⟩
  intro l hl hR
  have hN := (places_real_holds P hH hL ι W hW (fun _ => 0)).2
  have hN' := (places_real_holds P hH hL ι ({ W with fr := fr, cj := cj } : Wts ι) hW' (fun _ => 0)).2
  have hi : ({ W with fr := fr, cj := cj } : Wts ι).iW P l = W.iW P l := by
    funext τ
    unfold Wts.iW SizeData₂.depth
    obtain ⟨a1, a2⟩ := hN l hl hR.1 hR.2.2.1 τ
    obtain ⟨b1, b2⟩ := hN' l hl hR.1 hR.2.2.1 τ
    rw [a1, a2, b1, b2]
    rfl
  unfold Wts.coarseWeightBound
  rw [hi]
  rfl
end GlobalTheory
