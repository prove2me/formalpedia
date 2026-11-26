-- Prove2me | solution 1 for GlobalTheory.UnramSub.isDVR
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:47:00.869981+00:00
-- url     : https://prove2.me/submissions/a277298a-4f87-49fa-b1c8-94c11145b889

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnramSub
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.UnramSub
variable {V F : Type} [CommRing V] [Field F] {i : V →+* F}
theorem _root_.solution {T : Subring F} (h : UnramSub i T) : IsDiscreteValuationRing T := by
  first
    | (intros; simp [UnramSub])
    | (intros; unfold UnramSub; simp)
    | (intros; simp [UnramSub]; done)
    | (intros; ext; simp [UnramSub])
    | (intros; simp only [UnramSub]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [UnramSub])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [UnramSub])
    | (intros; unfold UnramSub; split_ifs <;> simp_all)
    | (intros; unfold UnramSub; positivity)
    | (intros; unfold UnramSub; ring)
    | (intros; unfold UnramSub; exact?)
    | (intros; aesop (add norm simp [UnramSub]))
    | (intros; simp [UnramSub] <;> aesop)
    | (intros; exact UnramSub.symm ..)
    | (intros; exact UnramSub.comm ..)
  trace "HIT_131_1"

